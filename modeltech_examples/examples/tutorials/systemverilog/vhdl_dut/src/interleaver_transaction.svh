class pkt_request #( int WIDTH = 8 , int PAYLD_SIZE = 203 )
  extends avm_transaction;

    typedef bit[WIDTH-1:0] payld_t [PAYLD_SIZE-1:0] ;
    typedef bit[WIDTH-1:0] sync_t;
    typedef pkt_request #( WIDTH , PAYLD_SIZE ) packet_t;

    rand sync_t              sync_byte;
    rand payld_t             payld_data;

    function avm_transaction clone();
        packet_t packet= new;
        packet.copy (this);
        return packet;
    endfunction

   function void copy (input packet_t packet);
        sync_byte = packet.sync_byte;
        payld_data = packet.payld_data;
    endfunction

    function string convert2string;
        string s;
        string int_s;

        begin

           s = { " Packet Sync Byte" };
           int_s.itoa( sync_byte );
           s = { s , " sync byte " , int_s };
           foreach (payld_data [i])
             begin
               int_s.itoa( payld_data[i] );
               s = { s , " , paylod data " , int_s , ";" };
             end

        end
        return s;

    endfunction

    function bit comp( input packet_t other );
        if( sync_byte != other.sync_byte ) begin
            return 0;
        end
        if( payld_data != other.payld_data ) begin
            return 0;
        end

        return 1;
    endfunction

endclass


class pkt_transaction #( WIDTH = 8 , PAYLD_SIZE = 203 ) extends avm_transaction;

    typedef bit[WIDTH-1:0] payld_t [PAYLD_SIZE-1:0] ;
    typedef bit[WIDTH-1:0] sync_t;
    typedef int delay_t [PAYLD_SIZE-1:0];
    typedef pkt_transaction #( WIDTH , PAYLD_SIZE ) transaction_t;

    rand sync_t              sync_byte;
    rand payld_t             payld_data;
    rand delay_t             xfer_dly;
    rand time                trStart;
    rand time                trEnd;
    rand int                 p_id;

    function delay_t init_delay;

      foreach (init_delay [i])
        init_delay[i] = 0;

    endfunction

    function payld_t init_payload;

      foreach (init_payload [i])
        init_payload[i] = 0;

    endfunction

    function new( int id,
                  sync_t sync,
                  payld_t payload,
                  delay_t delay,
                  time tstart,
                  time tend
                );

        p_id       = id;
        sync_byte  = sync;
        payld_data = payload;
        xfer_dly   = delay;
        trStart    = tstart;
        trEnd      = tend;

    endfunction


    function avm_transaction clone();
        transaction_t transaction = new ( p_id, sync_byte , payld_data, xfer_dly, trStart, trEnd );
        transaction.copy(this);
        return transaction;
    endfunction

   function void copy (input transaction_t t);
        p_id       = t.p_id;
        sync_byte  = t.sync_byte;
        payld_data = t.payld_data;
        xfer_dly   = t.xfer_dly;
        trStart    = t.trStart;
        trEnd      = t.trEnd;
    endfunction

    function string convert2string;
        string s;
        string int_s;

        begin

           s = { " Port ID " };
           int_s.itoa( p_id );
           s = { s , " sync byte " , int_s };
           int_s.itoa( trStart );
           s = { s , " Start Time " , int_s };
           int_s.itoa( trEnd );
           s = { s , " End Time " , int_s };

        end
        return s;

    endfunction

endclass
