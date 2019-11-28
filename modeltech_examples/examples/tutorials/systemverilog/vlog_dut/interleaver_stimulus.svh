class interleaver_stimulus  #( int WIDTH = 8 , int PAYLD_SIZE = 203 )
  extends avm_named_component;

  typedef pkt_request #( WIDTH , PAYLD_SIZE ) packet_t;
  typedef bit [WIDTH-1:0] payld_t [PAYLD_SIZE-1:0];

  avm_blocking_put_port #( packet_t ) put_port;

  function new( string name , avm_named_component parent );
    super.new( name , parent );
    put_port = new("put_port", this);
  endfunction

  bit doit = 1;

  function void stop;
    doit = 0;
  endfunction

  task generate_stimulus;

    packet_t  packet;
    payld_t   pkt_data;
    string    write_str;

    while (doit)
      begin
        for(int i=0; i<8; i++)
          begin
            if(i > 0)
              begin
                packet = new/*(8'hb8, pkt_data)*/;
                assert(packet.randomize()/* with { sync_byte == 8'hb8; }*/ )
                  else $error("Randomize failed.");
                packet.sync_byte = 8'hb8;
                $sformat( write_str , "%d" , packet.sync_byte );
                avm_report_message("Stimulus Generator sending packet to Driver" , write_str,,`__FILE__,`__LINE__);
                put_port.put(packet);
              end
            else
              begin
                packet = new/*(8'h47, pkt_data)*/;
                assert(packet.randomize()/* with {sync_byte == 8'h47; }*/ )
                  else $error("Randomize failed.");
                packet.sync_byte = 8'h47;
                $sformat( write_str , "%d" , packet.sync_byte );
                avm_report_message("Stimulus Generator sending packet to Driver" , write_str,,`__FILE__,`__LINE__ );
                put_port.put(packet);
              end
          end
      end
  endtask
endclass
