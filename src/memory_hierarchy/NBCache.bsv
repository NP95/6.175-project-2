import Vector::*;
import RegFile::*;

import Types::*;
import ProcTypes::*;
import MemTypes::*;
import CacheTypes::*;
import NBCacheTypes::*;

import Fifo::*;
import MessageFifo::*;
import StQ::*;
import LdBuff::*;

typedef enum {
    Ready,
    LdHitState,
    StHitState,
    StReqState,
    LdReqState
} NBCacheState deriving ( Bits, Eq );

module mkNBCache( CacheID c, MessageFifo#( n ) p2c, MessageFifo#( n ) c2p, NBCache ifc );
    
    Reg#( NBCacheState )   cacheState <- mkReg( Ready );
    Reg#( CacheMemResp )   memResp    <- mkRegU;
    Reg#( Maybe#( Addr ) ) linkAddr   <- mkReg( tagged Invalid );
    
    Vector#( CacheRows, Reg#( MSI ) )           state <- replicateM( mkReg( I ) );
    Vector#( CacheRows, Reg#( Maybe#( MSI ) ) ) waitp <- replicateM( mkReg( tagged Invalid ) );
    Vector#( CacheRows, Reg#( CacheTag ) )      tag   <- replicateM( mkRegU );
    Vector#( CacheRows, Reg#( CacheLine ) )     data  <- replicateM( mkRegU );
    
    Fifo#( 2, NBCacheResp ) hitQ <- mkCFFifo;
    StQ#( StQSz )           stQ  <- mkStQ;
    LdBuff#( LdBuffSz )     ldBf <- mkLdBuff;
    
    function Action return_hit( MemOp op, Addr a, Data d, NBCacheToken t );
        return (action
            hitQ.enq( NBCacheResp{ data: d, token: t } );
            if( op == Ll ) linkAddr <= tagged Valid a;
            //if( op == Sc ) linkAddr <= tagged Invalid;
        endaction);
    endfunction
    
    function Action update_cache_line( Addr a, MSI y, CacheLine d );
        return (action
            let t = getTag( a );
            let i = getIndex( a );
            if( linkAddr matches tagged Valid .linkA )
                if( getTag( linkA ) != t && getIndex( linkA ) == i )
                    linkAddr <= tagged Invalid;
            state[ i ] <= y;
            waitp[ i ] <= tagged Invalid;
            if( state[ i ] == I ) data[ i ] <= d;
        endaction);
    endfunction
    
    function Action update_cache_data( Addr a, MSI y, Data d );
        return (action
            let i = getIndex( a );
            let o = getOffset( a );
            state[ i ]      <= y;
            data [ i ][ o ] <= d;
        endaction);
    endfunction
    
    function Action send_downgrade_resp( Addr a, MSI y );
        return (action
            let i = getIndex( a );
            let d = ( state[ i ] == M ) ? data[ i ] : unpack( 0 );
            c2p.enq_resp( CacheMemResp{ child: c, addr: a, state: y, data: d } );
            state[ i ] <= y;
        endaction);
    endfunction
    
    function Bool can_send_upgrade_req( Addr a, MSI y );
        let idx = getIndex( a );
        return ( state[ idx ] < y || tag[ idx ] != getTag( a ) ) && waitp[ idx ] == tagged Invalid;
    endfunction
    
    function Action send_upgrade_req( Addr a, MSI y );
        return (action
            let i = getIndex( a );
            let t = getTag( a );
            tag  [ i ] <= t;
            waitp[ i ] <= tagged Valid y;
            c2p.enq_req( CacheMemReq{ child: c, addr: a, state: y } );
            if( state[ i ] != I && tag[ i ] != t )
                send_downgrade_resp( { tag[ i ], i, 0 }, I );
        endaction);
    endfunction
    
    rule doMsg( p2c.notEmpty && cacheState == Ready );
        if( p2c.first matches tagged Resp .d ) begin
            update_cache_line( d.addr, d.state, d.data );
            memResp <= d;
            cacheState <= LdHitState;
        end else if( p2c.first matches tagged Req .d ) begin
            let idx = getIndex( d.addr );
            let canDowngrade = tag[ idx ] == getTag( d.addr ) && state[ idx ] > d.state;
            if( canDowngrade ) send_downgrade_resp( d.addr, d.state );
        end
        p2c.deq;
    endrule
    
    rule onLdHit( cacheState == LdHitState );
        if( ldBf.searchHit( memResp.addr ) matches tagged Valid .hit ) begin
            ldBf.remove( tpl_1( hit ) );
            let r = tpl_2( hit );
            return_hit( r.op, r.addr, memResp.data[ getOffset( r.addr ) ], r.token );
        end else cacheState <= StHitState;
    endrule
    
    rule onStHit( cacheState == StHitState );
       let t = getTag  ( memResp.addr );
       let i = getIndex( memResp.addr );
       let hit = !stQ.empty && 
                 t == getTag  ( stQ.first.addr ) &&
                 i == getIndex( stQ.first.addr ) &&
                 state[ i ] == M;
       if( hit ) begin
           stQ.deq;
           let r = stQ.first;
           if ( r.op == Sc ) begin
               if ( linkAddr == tagged Valid r.addr) begin
                   update_cache_data( r.addr, memResp.state, r.data );
                   return_hit( r.op, r.addr, 1, r.token );
               end else return_hit( r.op, r.addr, 0, r.token );
           end else update_cache_data( r.addr, memResp.state, r.data );
       end else cacheState <= StReqState;
    endrule
    
    rule onStReq( cacheState == StReqState );
        if( !stQ.empty && can_send_upgrade_req( stQ.first.addr, M ) )
            send_upgrade_req( stQ.first.addr, M );
        cacheState <= LdReqState;
    endrule
    
    rule onLdReq( cacheState == LdReqState );
        if( ldBf.searchConflict( memResp.addr ) matches tagged Valid .c )
            if( can_send_upgrade_req( c.addr, S ) ) send_upgrade_req( c.addr, S );
        cacheState <= Ready;
    endrule
    
    method Action req( NBCacheReq r ) if( cacheState == Ready );
        let i = getIndex( r.addr );
        if( r.op == Ld || r.op == Ll ) begin
            let inCache = tag[ i ] == getTag( r.addr ) && state[ i ] != I;
            if( stQ.search( r.addr ) matches tagged Valid .d ) return_hit( r.op, r.addr, d, r.token );
            else if( inCache ) return_hit( r.op, r.addr, data[ i ][ getOffset( r.addr ) ], r.token );
            else begin
                ldBf.enq( LdBuffData{ op: r.op, addr: r.addr, token: r.token } );
                if( can_send_upgrade_req( r.addr, S ) ) send_upgrade_req( r.addr, S );
            end
       end else if( r.op == St ) begin
            let canUpdateCache = tag[ i ] == getTag( r.addr ) && state[ i ] == M && waitp[ i ] == tagged Invalid;
            if( canUpdateCache ) update_cache_data( r.addr, M, r.data );
            else begin
                stQ.enq( StQData{ op: r.op, addr: r.addr, data: r.data, token: unpack( 0 ) } );
                if( can_send_upgrade_req( r.addr, M ) ) send_upgrade_req( r.addr, M );
            end
        end else if( r.op == Sc ) begin
            if ( linkAddr == tagged Valid r.addr ) begin
                let canUpdateCache = tag[ i ] == getTag( r.addr ) && state[ i ] == M && waitp[ i ] == tagged Invalid;
                if( canUpdateCache ) begin
                    update_cache_data( r.addr, M, r.data );
                    return_hit( r.op, r.addr, 1, r.token );
                end else begin
                    stQ.enq( StQData{ op: r.op, addr: r.addr, data: r.data, token: r.token } );
                    if( can_send_upgrade_req( r.addr, M ) ) send_upgrade_req( r.addr, M );
                end
            end else return_hit( r.op, r.addr, 0, r.token );
        end
    endmethod
    
    method ActionValue#( NBCacheResp ) resp;
        hitQ.deq;
        return hitQ.first;
    endmethod
    
endmodule

