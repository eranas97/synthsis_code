class interleaver_score #(int PACKET_GEN_NUM=10, int WIDTH=8, PAYLD_SIZE=203)
  extends avm_subscriber #(pkt_transaction);

    typedef interleaver_score #(PACKET_GEN_NUM, WIDTH, PAYLD_SIZE) this_type;
    //typedef pkt_transaction #( WIDTH , PAYLD_SIZE ) transaction_t;
    typedef bit [WIDTH-1:0] packet [PAYLD_SIZE:0];

    avm_analysis_port #(pkt_transaction) ap;

    bit done = 0;
    bit error = 0;

    bit [WIDTH-1:0] pipe [0:1121];
    int pkt_rcvd_num = 0;
    string write_str, error_str;
    packet up, dn, exp_pkt;
    
    function new (string nm ="", avm_named_component p);
      super.new (nm, p);
      ap = new("ap", this);
    endfunction

    function void write(input pkt_transaction t);

      case (t.p_id) // p_id=0 is upstream port p=1 is downstream port
        32'd0:
          begin
            $sformat(write_str, "%h %d %d ", t.sync_byte, t.trStart, t.trEnd);
            avm_report_message("Upstream Packet Received by Scoreboard", write_str,,`__FILE__,`__LINE__);
            up[0] = t.sync_byte;
            for (int i=1; i<204; i++)
              up[i] = t.payld_data[i-1];
            exp_pkt = interleave(up,0);
          end
        32'd1:
          begin
            $sformat(write_str, "%h %d %d ", t.sync_byte, t.trStart, t.trEnd);
            avm_report_message("Downstream Packet Received by Scoreboard", write_str,,`__FILE__,`__LINE__);
            dn[0] = t.sync_byte;
            for (int i=1; i<204; i++)
             dn[i] = t.payld_data[i-1];
            assert (exp_pkt=== dn) pkt_rcvd_num += 1;
              else begin
                $sformat(error_str, "%d", $time);
                avm_report_error("Scoreboard Detected Packet Miscompare", error_str,,`__FILE__,`__LINE__);
                $error("Actual packet not equal to expected packet at time =%0t", $time);
                for (int i=0; i<204; i++)
                  $display("I = %d, UP_DATA = %h, DN_DATA =%h", i, up[i], dn[i]); 
                error = 1;
              end
            $display("NUMBER OF PACKETS CORRECTLY RECEIVED BY SCOREBOARD = %d", pkt_rcvd_num);
            if (pkt_rcvd_num >= PACKET_GEN_NUM)
              begin
              done = 1;
              $display("DONE = %d", done);
              end
          end
        default: $stop;
      endcase
    endfunction

    function /*automatic*/ packet interleave (input packet exp, input int k);
    //int k = 0;
      for (int i=0; i<=PAYLD_SIZE; i++)
      begin
        case (k)
          0: interleave[i] =  exp[i];
          1:
            begin
              interleave[i] =   pipe[16];
              for (int m=16; m>0; m--)
                pipe[m] =  pipe[m-1];
              pipe[0] =  exp[i];
            end
          2:
            begin
              interleave[i] =  pipe[50];
              for (int m=50; m>17; m--)
                pipe[m] =  pipe[m-1];
              pipe[17] =  exp[i];
            end
          3:
            begin
              interleave[i] =  pipe[101];
              for (int m=101; m>51; m--)
                pipe[m] =  pipe[m-1];
              pipe[51] =  exp[i];
            end
          4:
            begin
              interleave[i] =  pipe[169];
              for (int m=169; m>102; m--)
              pipe[m] =  pipe[m-1];
              pipe[102] =  exp[i];
            end
          5:
            begin
              interleave[i] =  pipe[254];
              for (int m=254; m>170; m--)
                pipe[m] =  pipe[m-1];
              pipe[170] =  exp[i];
            end
          6:
            begin
              interleave[i] =  pipe[356];
              for (int m=356; m>255; m--)
                pipe[m] =  pipe[m-1];
              pipe[255] =  exp[i];
            end
          7:
            begin
              interleave[i] =  pipe[475];
              for (int m=475; m>357; m--)
                pipe[m] =  pipe[m-1];
              pipe[357] =  exp[i];
            end
          8:
            begin
              interleave[i] =  pipe[611];
              for (int m=611; m>476; m--)
                pipe[m] =  pipe[m-1];
              pipe[476] =  exp[i];
            end
          9:
            begin
              interleave[i] =  pipe[764];
              for (int m=764; m>612; m--)
                pipe[m] =  pipe[m-1];
              pipe[612] =  exp[i];
            end
          10:
            begin
              interleave[i] =  pipe[934];
              for (int m=934; m>765; m--)
                pipe[m] =  pipe[m-1];
              pipe[765] =  exp[i];
            end
          11:
            begin
              interleave[i] =  pipe[1121];
              for (int m=1121; m>935; m--)
                pipe[m] =  pipe[m-1];
              pipe[935] =  exp[i];
            end
          default:
            begin
              $display("Reached the Default case in ERROR at time", $time);
              $stop;
            end
        endcase
        if (k == 11)
          k = 0;
        else
          k += 1;
      end
    endfunction : interleave

endclass
