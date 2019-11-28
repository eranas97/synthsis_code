class interleaver_nb_driver #( int WIDTH = 8, int PAYLD_SIZE = 203) extends avm_threaded_component;

    typedef interleaver_nb_driver #(WIDTH, PAYLD_SIZE) this_type;
    typedef pkt_request #( WIDTH , PAYLD_SIZE ) packet_t;
    typedef bit [WIDTH-1:0] sync_t;
    typedef  bit [WIDTH-1:0] payld_t [PAYLD_SIZE-1:0];
    typedef enum {READY_TO_SEND_PKT, SENDING_PKT} state_e;
    int        i = 0;
    int        di_high_prob, di_low_prob;
    int        do_high_prob, do_low_prob;

    virtual rdyacpt_pins_if #( .WIDTH( WIDTH )) pins_if;

    avm_nonblocking_get_port #( packet_t ) get_port;

    function new( string nm , avm_named_component p );
      super.new( nm , p );
      get_port = new("get_port", this);
    endfunction

    task run;

      packet_t   packet;
      state_e    pstate = READY_TO_SEND_PKT;

      fork
        forever begin
          @(posedge pins_if.upstream_mp.clk or negedge pins_if.upstream_mp.reset_n)
            if(!pins_if.upstream_mp.reset_n)
              begin
                pins_if.upstream_mp.rdy_di  <= 0;
                pins_if.upstream_mp.data_di <= 0;
                i = 0;
              end
            else
              case (pstate)
                READY_TO_SEND_PKT:
                  if (get_port.try_get(packet))
                    begin
                      assert(  randomize (di_high_prob) with {di_high_prob inside { [1:10] }; });
                      assert(  randomize (di_low_prob)  with {di_low_prob  inside { [1:10] }; });
                      assert(  randomize (do_high_prob) with {do_high_prob inside { [1:10] }; });
                      assert(  randomize (do_low_prob)  with {do_low_prob  inside { [1:10] }; });
                      pins_if.upstream_mp.rdy_di <= 1;
                      pins_if.upstream_mp.data_di <= packet.sync_byte;
                      pstate = SENDING_PKT;
                      i = 0;
                    end

                SENDING_PKT:
                  if(pins_if.upstream_mp.rdy_di & pins_if.upstream_mp.acpt_di)
                    begin
                      if (i==203)
                        pstate = READY_TO_SEND_PKT;
                      pins_if.upstream_mp.rdy_di <= 0;
                      pins_if.upstream_mp.data_di <= 0;
                    end
                  else
                    if (!pins_if.upstream_mp.rdy_di)
                      randcase
                        di_high_prob:
                          begin
                            pins_if.upstream_mp.rdy_di <= 1;
                            pins_if.upstream_mp.data_di <= packet.payld_data[i];
                            i += 1;
                          end
                        di_low_prob:
                          begin
                            pins_if.upstream_mp.rdy_di <= 0;
                            pins_if.upstream_mp.data_di <= 8'h00;
                          end
                      endcase
              endcase
        end

        // randomly drive the downstream acpt_do input
        forever begin
          @(posedge pins_if.downstream_mp.clk or negedge pins_if.downstream_mp.reset_n)
          if (!pins_if.downstream_mp.reset_n)
            pins_if.downstream_mp.acpt_do <= 1'b0;
          else
            begin
              if (pins_if.downstream_mp.rdy_do && pins_if.downstream_mp.acpt_do)
                pins_if.downstream_mp.acpt_do <= 0;
              if (!pins_if.downstream_mp.acpt_do)
                randcase
                  do_high_prob: pins_if.downstream_mp.acpt_do <= 1;
                  do_low_prob : pins_if.downstream_mp.acpt_do <= 0;
                endcase
            end
        end
    join
  endtask
endclass

	
