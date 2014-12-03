import CacheTypes::*;
import Fifo::*;

module mkMessageFifo( MessageFifo#( n ) );
    
    Fifo#( n, CacheMemResp ) respFifo <- mkCFFifo;
    Fifo#( n, CacheMemReq )  reqFifo  <- mkCFFifo;
    
    method Action enq_resp( CacheMemResp d );
        respFifo.enq( d );
    endmethod
    
    method Action enq_req( CacheMemReq d );
        reqFifo.enq( d );
    endmethod
    
    method Bool hasResp = respFifo.notEmpty;
    method Bool hasReq = reqFifo.notEmpty;
    method Bool notEmpty = respFifo.notEmpty || reqFifo.notEmpty;
    
    method CacheMemMessage first;
        return respFifo.notEmpty ? tagged Resp respFifo.first : tagged Req reqFifo.first;
    endmethod
    
    method Action deq if( respFifo.notEmpty || reqFifo.notEmpty );
        if( respFifo.notEmpty ) respFifo.deq;
        else reqFifo.deq;
    endmethod
    
endmodule

