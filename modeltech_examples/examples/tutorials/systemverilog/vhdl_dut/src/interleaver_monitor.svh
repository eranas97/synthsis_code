class interleaver_monitor #(int WIDTH=8, int PAYLD_SIZE=203) extends avm_threaded_component;

    typedef pkt_transaction #( WIDTH , PAYLD_SIZE ) transaction_t;
    typedef enum {WAIT_FOR_SYNC, WAIT_FOR_DATA} state_e;
    typedef int delay_t [0:PAYLD_SIZE-1];
    typedef bit [WIDTH-1:0] payld_t [PAYLD_SIZE-1:0];
    typedef bit [WIDTH-1:0] sync_t ;
    int i=0, j=0, k=0, l=0; 
    virtual rdyacpt_pins_if #(.WIDTH( WIDTH )) pins_if;

    // Standard implementation of an analysis port.
     avm_analysis_port #( transaction_t ) ap;

    function new( string name = "" , avm_named_component parent );
      super.new( name , parent );
      ap = new("ap", this);
    endfunction

    task run; 

      transaction_t    uptr, dntr;
      payld_t          up_mem, dn_mem;
      sync_t           up_sync, dn_sync;
      delay_t          up_dly, dn_dly;
      state_e          upstate, dnstate;
      time             up_trStart, dn_trStart;
      upstate = WAIT_FOR_SYNC;
      dnstate = WAIT_FOR_SYNC;

      fork
        forever begin
          @(posedge pins_if.monitor_mp.clk or negedge pins_if.monitor_mp.reset_n)
          if (!pins_if.monitor_mp.reset_n)
            begin
              i = 0;
              j = 0;
              upstate = WAIT_FOR_SYNC;
            end
          else
            case (upstate)
              WAIT_FOR_SYNC:
                if (pins_if.monitor_mp.rdy_di & pins_if.monitor_mp.acpt_di)
                  if (pins_if.monitor_mp.data_di == 8'h47 || pins_if.monitor_mp.data_di == 8'hb8)
                    begin 
                      up_sync = pins_if.monitor_mp.data_di;
                      up_trStart = $time;
                      upstate = WAIT_FOR_DATA;
                      j = 0;
                    end
              WAIT_FOR_DATA:
                if (pins_if.monitor_mp.rdy_di & pins_if.monitor_mp.acpt_di)
                  begin
                    up_dly[i] = j;
                    up_mem[i] = pins_if.monitor_mp.data_di;
                    if (i == 202)
                      begin
                        uptr = new(0, up_sync, up_mem, up_dly, up_trStart, $time);
                        $display("UPSTREAM MONITOR AP PORT WRITE ID=%d SYNC=%h START=%d END=%d", uptr.p_id,
                                  uptr.sync_byte, uptr.trStart, uptr.trEnd);
                        ap.write(uptr);
                        upstate = WAIT_FOR_SYNC;
                        i = 0;
                      end
                  else
                      begin
                        i +=1;
                        j = 0;
                      end
                  end
                else
                  j += 1;
            endcase
        end
  
        forever begin
          @(posedge pins_if.monitor_mp.clk or negedge pins_if.monitor_mp.reset_n)
            if (!pins_if.monitor_mp.reset_n)
              begin
                k = 0;
                l = 0;
                dnstate = WAIT_FOR_SYNC;
              end
            else
              case (dnstate)
                WAIT_FOR_SYNC:
                  if (pins_if.monitor_mp.rdy_do & pins_if.monitor_mp.acpt_do)
                  if (pins_if.monitor_mp.data_do == 8'h47 || pins_if.monitor_mp.data_do == 8'hb8)
                    begin 
                      dn_sync = pins_if.data_do;
                      dn_trStart = $time;
                      dnstate = WAIT_FOR_DATA;
                      l = 0;
                    end
                WAIT_FOR_DATA:
                  if (pins_if.monitor_mp.rdy_do & pins_if.monitor_mp.acpt_do)
                    begin
                      dn_dly[k] = l;
                      dn_mem[k] = pins_if.monitor_mp.data_do;
                      if (k == 202)
                        begin
                          dntr = new(1, dn_sync, dn_mem, dn_dly, dn_trStart, $time);
                          ap.write(dntr);
                          dnstate = WAIT_FOR_SYNC;
                          k = 0;
                          l = 0;
                        end
                      else
                        begin
                          k +=1;
                          l = 0;
                        end
                    end
                  else
                    l += 1;
              endcase
        end
      join
    endtask
endclass

