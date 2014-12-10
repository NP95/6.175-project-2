import Types::*;
import ProcTypes::*;
import CacheTypes::*;
import NBCacheTypes::*;
import MemTypes::*;
import Fifo::*;
import Vector::*;

import SACache::*;

module mkParentProtocolProcessor( MessageFifo#( n ) r2m,
                                  MessageFifo#( n ) m2r,
                                  WideMem _mem,
                                  Empty ifc );
    
    L2Cache mem <- mkSACache( _mem, True );
    
    Reg#( Bool ) memResp <- mkReg( False );
    
    Vector#( NumCaches, Vector#( CacheRows, Reg#( MSI ) ) )
        state <- replicateM( replicateM( mkReg( I ) ) );
    Vector#( NumCaches, Vector#( CacheRows, Reg#( Maybe#( MSI ) ) ) )
        waitc <- replicateM( replicateM( mkReg( tagged Invalid ) ) );
    Vector#( NumCaches, Vector#( CacheRows, Reg#( CacheTag ) ) )
        tag   <- replicateM( replicateM( mkRegU ) );
    
    function MSI getChild( CacheID c, Addr a );
        let i = getIndex( a );
        return tag[ c ][ i ] == getTag( a ) ? state[ c ][ i ] : I;
    endfunction
    
    function Action setChild( CacheID c, Addr a, MSI y );
        return (action
          state[ c ][ getIndex( a ) ] <= y;
          tag[ c ][ getIndex( a ) ] <= getTag( a );
        endaction);
    endfunction
    
    function Maybe#( MSI ) getWaitc( CacheID c, Addr a );
        let i = getIndex( a );
        return tag[ c ][ i ] == getTag( a ) ? waitc[ c ][ i ] : tagged Invalid;
    endfunction
    
    function Action setWaitc( CacheID c, Addr a, Maybe#( MSI ) w );
        return ( action waitc[ c ][ getIndex( a ) ] <= w; endaction );
    endfunction
    
    function Bool noWaitc( Addr a );
        Bool r = True;
        for( Integer j = 0; r && j < valueOf( NumCaches ); j = j + 1 )
            if( getWaitc( fromInteger( j ), a ) matches tagged Valid .x )
                r = False;
        return r;
    endfunction
    
    function Bool isCompatible( MSI x, MSI y );
        if( x == I || y == I ) return True;
        else if( x == S ) return y == S;
        else if( y == S ) return x == S;
        else return False;
    endfunction
    
    function Maybe#( CacheID ) firstIncompatible( CacheID c, Addr a, MSI y );
        Maybe#( CacheID ) r = tagged Invalid;
        for( Integer i = 0; r == tagged Invalid && i < valueOf( NumCaches ); i = i + 1 ) begin
            if( fromInteger( i ) != c && !isCompatible( getChild( fromInteger( i ), a ), y ) )
                r = tagged Valid fromInteger( i );
        end
        return r;
    endfunction
    
    rule twofoursix;
        if( r2m.first matches tagged Req .d) begin
            let c = d.child;
            let a = d.addr;
            let y = d.state;
            if( noWaitc( a ) ) begin
                if( getChild( c, a ) < y ) begin // Rule 2
                    let i = firstIncompatible( c, a, y );
                    if( i matches tagged Invalid ) begin
                        if( getChild( c, a ) == I ) begin
                            if( memResp ) begin
                                let dat <- mem.resp;
                                let r = CacheMemResp{ child: c, addr: a, state: y, data: dat };
                                m2r.enq_resp( r );
                                setChild( c, a, y );
                                r2m.deq;
                                memResp <= False;
                            end else begin
                                mem.req( toWideMemReq( MemReq{ op: Ld, addr: a, data: ? } ) );
                                memResp <= True;
                            end
                        end else begin
                            let r = CacheMemResp{ child: c, addr: a, state: y, data: ? };
                            m2r.enq_resp( r );
                            setChild( c, a, y );
                            r2m.deq;
                        end
                    end else if( i matches tagged Valid .nc ) begin
                        let ny = (y == M ? I : S);
                        m2r.enq_req( CacheMemReq{ child: nc, addr: a, state: ny } );
			setWaitc( nc, a, tagged Valid ny );
                    end
                end else if( getChild( c, a ) > y ) begin // Rule 4
                    setWaitc( c, a, tagged Valid y );
                    m2r.enq_req( CacheMemReq{ child: c, addr: a, state: y} );
                end
            end
        end else if ( r2m.first matches tagged Resp .d ) begin
            let c = d.child;
            let a = d.addr;
            let y = d.state;
            let dat = d.data;
            if( getChild( c, a ) > y ) begin // Rule 6
                r2m.deq;
                Addr addr = { getTag( a ), getIndex( a ), '0 };
                if( getChild( c, a ) == M )
                    mem.req( WideMemReq{ write_en: '1, addr: addr, data: dat } );
                setChild( c, a, y );
                if( isValid( getWaitc( c, a ) ) && fromMaybe( ?, getWaitc( c, a ) ) >= y )
                    setWaitc( c, a, tagged Invalid );
            end
        end
    endrule
    
endmodule

