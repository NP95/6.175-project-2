import Types::*;
import ProcTypes::*;
import CacheTypes::*;
import NBCacheTypes::*;
import Fifo::*;
import Vector::*;

typedef 4 NumSets;
typedef Bit#(TLog#(NumSets)) SetIdx;
typedef SetIdx Age;

typedef enum { Ready, WriteBack, SendFillReq, WaitFillResp } SACacheStatus deriving ( Bits, Eq );

interface L2Cache;
    method Action req( WideMemReq r );
    method ActionValue#( CacheLine ) resp;
endinterface

module mkSACache( WideMem mem, L2Cache ifc );
    
    Vector#(NumSets,Vector#(CacheRows,Reg#(Maybe#(CacheTag)))) tag <- replicateM(replicateM(mkReg(tagged Invalid)));    
    Vector#(NumSets,Vector#(CacheRows,Reg#(CacheLine))) data <- replicateM(replicateM(mkReg(replicate(0))));
    Vector#(NumSets,Vector#(CacheRows,Reg#(Bool))) dirty <- replicateM(replicateM(mkReg(False)));
    Vector#(NumSets,Vector#(CacheRows,Reg#(Age))) age <- replicateM(replicateM(mkReg(3)));
    
    Fifo#( 2, CacheLine ) hitQ <- mkCFFifo;
    
    Reg#( WideMemReq ) missReq <- mkRegU;
    Reg#( SACacheStatus ) status <- mkReg( Ready );
    Reg#( SetIdx ) lru <- mkRegU;
      
    function SetIdx getLRUSetIdx( CacheIndex idx );
        SetIdx set_idx = 0;
        for( Integer i = 0; i < valueOf( NumSets ); i = i + 1 ) begin
            if( age[fromInteger(i)][idx] == 3 )
                set_idx = fromInteger(i);
        end
        return set_idx;
    endfunction
    
    function Maybe#( SetIdx ) getTagSetIdx( CacheTag t, CacheIndex idx );
        Maybe#( SetIdx ) l = tagged Invalid;
        for( Integer i = 0; i < valueOf( NumSets ); i = i + 1 )
            if( tag[fromInteger(i)][idx] == tagged Valid t )
                l = tagged Valid fromInteger(i);
        return l;
    endfunction
    
    function Action zeroAge( CacheIndex idx, SetIdx s);
        return ( action
            for( Integer i = 0; i < valueOf( NumSets ); i = i + 1 )
                if( age[fromInteger(i)][idx] < age[s][idx] )
                    age[fromInteger(i)][idx] <= age[fromInteger(i)][idx] + 1;
            age[s][idx] <= 0;
        endaction );
    endfunction
    
    rule writeBack( status == WriteBack );
        let s = getIndex( missReq.addr );
        if( dirty[lru][s] )
          if(tag[lru][s] matches tagged Valid .t) 
            mem.req(WideMemReq{write_en: '1, addr: { t, s, 0 }, data: data[lru][s]});

        status <= SendFillReq;
    endrule
    
    rule sendFillReq( status == SendFillReq );
        let r = missReq;
        r.write_en = 0;
        mem.req( r );
        status <= WaitFillResp;
    endrule
    
    rule waitFillResp( status == WaitFillResp );
        let t  = getTag( missReq.addr );
        let s  = getIndex( missReq.addr );
        let ld = missReq.write_en == 0;
        let d <- mem.resp; 
        if(ld)
            hitQ.enq( d );
        else
            d = missReq.data;
        
        tag  [lru][s] <= tagged Valid t;
        data [lru][s] <= d;
        dirty[lru][s] <= !ld;

        zeroAge(s,lru);
        status <= Ready;        
    endrule
    
    method Action req( WideMemReq r ) if( status == Ready );
        let t = getTag( r.addr );
        let s = getIndex( r.addr );
        if( getTagSetIdx( t, s ) matches tagged Valid .l ) begin
            if( r.write_en == 0 )
                hitQ.enq( data[l][s] );
            else begin
                data[l][s] <= r.data;
                dirty[l][s] <= True;
            end
            zeroAge(s, l);
        end else begin
            let lru_tmp = getLRUSetIdx( s );
            lru <= lru_tmp;
            missReq <= r;
            if (tag[lru_tmp][s] matches tagged Valid .tg) status <= WriteBack;
            else status <= SendFillReq;
        end
    endmethod
    
    method ActionValue#( CacheLine ) resp;
        hitQ.deq;
        return hitQ.first;
    endmethod
    
endmodule

