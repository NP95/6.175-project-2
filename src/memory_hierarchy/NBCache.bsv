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

module mkNBCache( CacheID c,
                  MessageFifo#( n ) p2c,
                  MessageFifo#( n ) c2p,
                  NBCache ifc );
    
    Reg#( NBCacheState ) cacheState <- mkReg( Ready );
    Reg#( CacheMemResp ) memResp <- mkRegU;
    
    Vector#( NBCacheSize, Reg#( MSI ) )           state <- replicateM( mkReg( I ) );
    Vector#( NBCacheSize, Reg#( Maybe#( MSI ) ) ) waitp <- replicateM( mkReg( tagged Invalid ) );
    Vector#( NBCacheSize, Reg#( CacheTag ) )      tag   <- replicateM( mkRegU );
    Vector#( NBCacheSize, Reg#( CacheLine ) )     data  <- replicateM( mkRegU );
    
    Fifo#( 2, NBCacheResp ) hitQ <- mkCFFifo;
    StQ#( StQSz )           stQ  <- mkStQ;
    LdBuff#( LdBuffSz )     ldBf <- mkLdBuff;
    
    function Action return_hit( Data d, NBCacheToken t );
        return (action hitQ.enq( NBCacheResp{ data: d, token: t } ); endaction);
    endfunction
    
    function Action update_cache_line( Addr a, MSI y, CacheLine d );
        return (action
            let idx = getIndex( a );
            state[ idx ] <= y;
            waitp[ idx ] <= tagged Invalid;
            tag  [ idx ] <= getTag( a );
            data [ idx ] <= d;
        endaction);
    endfunction
    
    function Action update_cache_data( Addr a, MSI y, Data d );
        return (action
            let idx = getIndex( a );
            let off = getOffset( a );
            state[ idx ]        <= y;
            data [ idx ][ off ] <= d;
        endaction);
    endfunction
    
    function Action send_downgrade_resp( Addr a, MSI y );
        return (action
            let idx = getIndex( a );
            let dat = ( state[ idx ] == M ) ? data[ idx ] : unpack( 0 );
            c2p.enq_resp( CacheMemResp{ child: c, addr: a, state: y, data: dat } );
            state[ idx ] <= y;
        endaction);
    endfunction
    
    function Bool can_send_upgrade_req( Addr a, MSI y );
        let idx = getIndex( a );
        return ( state[ idx ] < y || tag[ idx ] != getTag( a ) ) && waitp[ idx ] == tagged Invalid;
    endfunction
    
    function Action send_upgrade_req( Addr a, MSI y );
        return (action
            let idx  = getIndex( a );
            let cTag = getTag( a );
            tag  [ idx ] <= getTag( a );
            waitp[ idx ] <= tagged Valid y;
            c2p.enq_req( CacheMemReq{ child: c, addr: a, state: y } );
            if( state[ idx ] != I && tag[ idx ] != cTag )
                send_downgrade_resp( { tag[ idx ], idx, 0 }, I );
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
            return_hit( memResp.data[ getOffset( tpl_2( hit ).addr ) ], tpl_2( hit ).token );
        end else cacheState <= StHitState;
    endrule
    
    rule onStHit( cacheState == StHitState );
       let idx = getIndex( memResp.addr );
       if( !stQ.empty && memResp.addr >> 6 == stQ.first.addr >> 6 && state[ idx ] == M  ) begin
           stQ.deq;
           update_cache_data( stQ.first.addr, memResp.state, stQ.first.data );
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
        if( r.op == Ld ) begin
            let idx = getIndex( r.addr );
            let inCache = tag[ idx ] == getTag( r.addr ) && state[ idx ] != I;
            if( stQ.search( r.addr ) matches tagged Valid .dat ) return_hit( dat, r.token );
            else if( inCache ) return_hit( data[ idx ][ getOffset( r.addr ) ], r.token );
            else begin
                ldBf.enq( LdBuffData{ addr: r.addr, op: Ld, token: r.token } );
                if( can_send_upgrade_req( r.addr, S ) ) send_upgrade_req( r.addr, S );
            end
        end else if( r.op == St ) begin
            let idx = getIndex( r.addr );
            let canUpdateCache = tag[ idx ] == getTag( r.addr ) && state[ idx ] == M && stQ.empty;
            if( canUpdateCache ) update_cache_data( r.addr, M, r.data );
            else begin
                stQ.enq( StQData{ op: St, addr: r.addr, data: r.data, token: ? } ); // TODO
                if( can_send_upgrade_req( r.addr, M ) ) send_upgrade_req( r.addr, M );
            end
        end
    endmethod
    
    method ActionValue#( NBCacheResp ) resp;
        hitQ.deq;
        return hitQ.first;
    endmethod
    
endmodule

