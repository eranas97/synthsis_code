typedef enum {idle, send_bypass, load0, send0, load1, send1, load2,
                    send2, load3, send3, load4, send4, load5, send5, load6,
                    send6, load7, send7, load8, send8, load9, send9, load10,
                    send10, load_bypass, wait_idle
                   } fsm_state;

module interleaver_props (
  input clk, in_hs, out_hs, 
  input[7:0] input_down_data, do_reg,
  input [4:0] int_state_vec
);

fsm_state int_state;

assign
int_state = fsm_state'(int_state_vec);

sequence sync_in_valid;
(input_down_data == 8'h47 || input_down_data == 8'hb8);
endsequence

// Check for sync byte at the start of a every packet
property pkt_start_check;
@(posedge clk) (int_state == idle && in_hs) |-> (sync_in_valid);
endproperty

assert property(pkt_start_check);

// Check that every packet is 204 bytes long
property pkt_length_check;
@(posedge clk) (int_state == idle && in_hs) |-> (sync_in_valid ##1 (in_hs && int_state != idle)[=203]);
endproperty

assert property(pkt_length_check);

// Check for sync byte being bypassed
// pl property sync_bypass_check = always {in_hs && int_state == idle &&
//   (input_down_data == 8'h47 || input_down_data == 8'hb8)} |=>
//   {(int_state == send_bypass && out_hs && (do_reg == 8'h47 || do_reg == 8'hb8))[=1]};
// pl assert sync_bypass_check;
property sync_bypass_check;
@(posedge clk) (int_state == idle && in_hs) |-> (sync_in_valid |=>
               (int_state == send_bypass && out_hs && (do_reg == 8'h47 || do_reg == 8'hb8))[=1]);
endproperty

assert property(sync_bypass_check);

sequence s_interleave_sm;
@(posedge clk) $rose(((int_state == idle || int_state == load_bypass) && in_hs)) ##1
              (int_state == send_bypass && out_hs)[->1] ##1
              (int_state == load0  && in_hs)[->1] ##1 (int_state == send0  && out_hs)[->1] ##1
              (int_state == load1  && in_hs)[->1] ##1 (int_state == send1  && out_hs)[->1] ##1
              (int_state == load2  && in_hs)[->1] ##1 (int_state == send2  && out_hs)[->1] ##1
              (int_state == load3  && in_hs)[->1] ##1 (int_state == send3  && out_hs)[->1] ##1
              (int_state == load4  && in_hs)[->1] ##1 (int_state == send4  && out_hs)[->1] ##1
              (int_state == load5  && in_hs)[->1] ##1 (int_state == send5  && out_hs)[->1] ##1
              (int_state == load6  && in_hs)[->1] ##1 (int_state == send6  && out_hs)[->1] ##1
              (int_state == load7  && in_hs)[->1] ##1 (int_state == send7  && out_hs)[->1] ##1
              (int_state == load8  && in_hs)[->1] ##1 (int_state == send8  && out_hs)[->1] ##1
              (int_state == load9  && in_hs)[->1] ##1 (int_state == send9  && out_hs)[->1] ##1
              (int_state == load10 && in_hs)[->1] ##1 (int_state == send10 && out_hs)[->1];
endsequence

cover property (s_interleave_sm);

covergroup sm_cvg @(posedge clk);
  coverpoint int_state
  {
    bins idle_bin = {idle};
    bins load_bins = {load_bypass, load0, load1, load2, load3, load4, load5, load6, load7, load8, load9, load10};
    bins send_bins = {send_bypass, send0, send1, send2, send3, send4, send5, send6, send7, send8, send9, send10};
    bins others = {wait_idle};
  option.at_least = 500;

  }
  coverpoint in_hs;
  coverpoint out_hs;

  in_hsXint_state: cross in_hs, int_state;
  out_hsXint_state: cross out_hs, int_state;
  //option.comment = "covered it";

endgroup

sm_cvg sm_cvg_c1 = new;


endmodule
