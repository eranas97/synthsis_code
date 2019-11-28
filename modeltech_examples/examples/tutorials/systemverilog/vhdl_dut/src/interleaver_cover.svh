class interleaver_cover #(int WIDTH = 8, int PAYLD_SIZE=203) extends avm_subscriber #(pkt_transaction);

    typedef interleaver_cover #(WIDTH , PAYLD_SIZE) this_type;
    typedef pkt_transaction #( WIDTH , PAYLD_SIZE ) transaction_t;
    typedef bit [WIDTH-1:0] payld_t [PAYLD_SIZE-1:0];
    typedef bit [WIDTH-1:0] sync_t;
    typedef int delay_t[PAYLD_SIZE-1:0];

    avm_analysis_port #(transaction_t) ap;
 
    bit [WIDTH-1:0]  upcov_data, dncov_data;
    bit [WIDTH-1:0]  upcov_sync, dncov_sync;
    int              up_delay, dn_delay;
    payld_t          up_mem, dn_mem;
    delay_t          up_dly, dn_dly;


    // Upstream packet covergroup
    covergroup up_cvg;
        option.auto_bin_max = 256;
        coverpoint upcov_data;
        coverpoint upcov_sync {
          bins sync [] ={ 71, 184 };
          bins illegal = default;
        }
        coverpoint up_delay {
          bins short  [] = {[0:4]};
          bins sh2med [] = {[5:9]};
          bins md2lng [] = {[10:14]};
          bins long   [] = {[15:19]};
          bins vrylng  = default;
        }
    endgroup

    // Upstream packet covergroup
    covergroup dn_cvg;
        option.auto_bin_max = 256;
        coverpoint dncov_data;
        coverpoint dncov_sync {
          bins sync [] ={ 71, 184 };
          bins illegal = default;
        }
        coverpoint dn_delay {
          bins short  [] = {[0:4]};
          bins sh2med [] = {[5:9]};
          bins md2lng [] = {[10:14]};
          bins long   [] = {[15:19]};
          bins vrylng = default;
        }
    endgroup

    function new (string nm ="", avm_named_component p);
      super.new (nm, p);
      ap = new("ap", this);
      up_cvg = new;
      dn_cvg = new;
    endfunction

    function void write(transaction_t t);
      case (t.p_id) // p_id=0 is upstream port p=1 is downstream port
        32'd0:
          begin
            upcov_sync = t.sync_byte;
            up_mem = t.payld_data;
            up_dly = t.xfer_dly;
            foreach (up_mem [i])
              begin
                upcov_data = up_mem[i];
                up_delay   = up_dly[i];
                up_cvg.sample;
             end
          end
        32'd1:
          begin
            dncov_sync = t.sync_byte;
            dn_mem = t.payld_data;
            dn_dly = t.xfer_dly;
            foreach (dn_mem [i])
              begin
                dncov_data = dn_mem[i];
                dn_delay   = dn_dly[i];
                dn_cvg.sample;
             end
          end
      endcase
    endfunction

endclass
