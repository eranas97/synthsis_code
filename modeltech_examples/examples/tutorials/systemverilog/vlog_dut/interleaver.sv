module interleaver #(parameter integer BUG=0) (input enable, interface pins);

typedef enum {idle, send_bypass, load0, send0, load1, send1, load2,
                    send2, load3, send3, load4, send4, load5, send5, load6,
                    send6, load7, send7, load8, send8, load9, send9, load10,
                    send10, load_bypass, wait_idle
                   } fsm_state;

fsm_state nxt_state, int_state;

reg [7:0] do_reg;
reg [10:0] push;

wire in_hs;
wire out_hs;
wire in_acpt;
wire out_acpt;
wire out_rdy;
wire in_rdy;
wire pkt_cen;
wire pkt_zero;
wire pkt_ld_n;
wire ram_re;
wire [7:0] fifo_data;
wire [3:0] data_sel;
wire [7:0] pkt_cnt;
wire [7:0] input_down_data;

// Possible sync byte received
sequence sync_in_valid (data);
(data == 8'h47 || data == 8'hb8);
endsequence

// Check for sync byte at the start of a every packet
property pkt_start_check;
@(posedge pins.clk) (int_state == idle && in_hs) |-> (sync_in_valid(input_down_data));
endproperty

assert property(pkt_start_check);

// Check that every packet is 204 bytes long
property pkt_length_check;
@(posedge pins.clk) (int_state == idle && in_hs) |-> (sync_in_valid(input_down_data)
   ##1 (in_hs && int_state != idle)[=203]);
endproperty

assert property(pkt_length_check);

// Check for sync byte being bypassed
property sync_bypass_check;
@(posedge pins.clk) (int_state == idle && in_hs) ##0 (sync_in_valid(input_down_data)) |=>
               (int_state == send_bypass && out_hs && (do_reg == 8'h47 || do_reg == 8'hb8))[=1];
endproperty

assert property(sync_bypass_check);

sequence s_interleave_sm;
@(posedge pins.clk) $rose(((int_state == idle || int_state == load_bypass) && in_hs)) ##1
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

covergroup sm_transitions_cvg @(posedge pins.clk);
  coverpoint int_state  {
    bins idle_st = (idle => send_bypass[->1] => load0[->1] => send0[->1] =>
                   load1[->1] => send1[->1] => load2[->1] => send2[->1] =>
                   load3[->1] => send3[->1] => load4[->1] => send4[->1] =>
                   load5[->1] => send5[->1] => load6[->1] => send6[->1] =>
                   load7[->1] => send7[->1] => load8[->1] => send8[->1] =>
                   load9[->1] => send9[->1] => load10[->1] => send10[->1]);
    bins bypass_st = (load_bypass => send_bypass[->1] => load0[->1] => send0[->1] =>
                   load1[->1] => send1[->1] => load2[->1] => send2[->1] =>
                   load3[->1] => send3[->1] => load4[->1] => send4[->1] =>
                   load5[->1] => send5[->1] => load6[->1] => send6[->1] =>
                   load7[->1] => send7[->1] => load8[->1] => send8[->1] =>
                   load9[->1] => send9[->1] => load10[->1] => send10[->1]);
  }
endgroup

covergroup sm_cvg @(posedge pins.clk);
  coverpoint int_state;
  coverpoint in_hs {
   bins valid = {1};
   //ignore_bins invalid = default;
  }
  coverpoint out_hs {
   bins valid = {1};
   //ignore_bins invalid = default;
  }
  in_hsXint_state: cross int_state, in_hs;
  out_hsXint_state: cross int_state, out_hs;
  option.at_least = 500;
  option.comment = "covered it";

endgroup

sm_transitions_cvg sm_cvg_c1 = new;
sm_cvg sm_cvg_c2 = new;

assign 
  in_hs = in_acpt & in_rdy,
  out_hs = out_acpt & out_rdy,
  in_acpt = int_state == idle   || int_state == load_bypass || 
            int_state == load0  || int_state == load1  ||
            int_state == load2  || int_state == load3  ||
            int_state == load4  || int_state == load5  ||
            int_state == load6  || int_state == load7  ||
            int_state == load8  || int_state == load9  ||
            int_state == load10, 

  out_rdy = int_state == send_bypass || int_state == send0 ||
            int_state == send1  || int_state == send2  ||
            int_state == send3  || int_state == send4  ||
            int_state == send5  || int_state == send6  ||
            int_state == send7  || int_state == send8  ||
            int_state == send9  || int_state == send10,
                   

  pkt_cen  = pins.reset_n & in_hs & ~pkt_zero,
  pkt_ld_n = ~(int_state == idle),
  data_sel = int_state == load1  || int_state == send0 ? 4'b0001 :
             int_state == load2  || int_state == send1 ? 4'b0010 :
             int_state == load3  || int_state == send2 ? 4'b0011 :
             int_state == load4  || int_state == send3 ? 4'b0100 :
             int_state == load5  || int_state == send4 ? 4'b0101 :
             int_state == load6  || int_state == send5 ? 4'b0110 :
             int_state == load7  || int_state == send6 ? 4'b0111 :
             int_state == load8  || int_state == send7 ? 4'b1000 :
             int_state == load9  || int_state == send8 ? 4'b1001 :
             int_state == load10 || int_state == send9 ? 4'b1010 :
             4'b0000,

  ram_re = out_hs && (int_state == send0  || int_state == send1 ||
                      int_state == send2  || int_state == send3 ||
                      int_state == send4  || int_state == send5 ||
                      int_state == send6  || int_state == send7 ||
                      int_state == send8  || int_state == send9 ||
                      int_state == send10 || int_state == send_bypass);

always @(posedge pins.clk)
if(in_hs && (int_state == idle || int_state == load_bypass))
  do_reg <= input_down_data;
else if(|push)
  do_reg <= fifo_data;
else
  do_reg <= do_reg;
       
wire fsm_clk = pins.clk;
wire fsm_reset_n = pins.reset_n;
always @(posedge fsm_clk or negedge fsm_reset_n)
if(!fsm_reset_n)
  int_state <= idle;
else
  int_state <= nxt_state;

always @(*)
begin
  nxt_state = int_state;
  push = 11'b0;
  case (int_state)
    idle:
       if(in_hs)
         nxt_state = send_bypass;
       else
         nxt_state = idle;
    send_bypass:
      if(out_hs)
        if(enable)
          nxt_state = load0;
        else
          nxt_state = idle;
    load0:
       if(in_hs)
         begin
           nxt_state = send0;
           push[0] = 1'b1;
         end
    send0:
      if(out_hs)
        nxt_state = load1;
    load1:
       if(in_hs)
         begin
           nxt_state = send1;
           push[1] = 1'b1;
         end
    send1:
      if(out_hs)
        nxt_state = load2;
    load2:
       if(in_hs)
         begin
           nxt_state = send2;
           push[2] = 1'b1;
         end
    send2:
      if(out_hs)
        nxt_state = load3;
    load3:
       if(in_hs)
         begin
           nxt_state = send3;
           push[3] = 1'b1;
         end
    send3:
      if(out_hs)
        nxt_state = load4;
    load4:
       if(in_hs)
         begin
           nxt_state = send4;
           push[4] = 1'b1;
         end
    send4:
      if(out_hs)
        nxt_state = load5;
    load5:
       if(in_hs)
         begin
           nxt_state = send5;
           push[5] = 1'b1;
         end
    send5:
      if(out_hs)
        nxt_state = load6;
    load6:
       if(in_hs)
         begin
           nxt_state = send6;
           push[6] = 1'b1;
         end
    send6:
      if(out_hs)
        nxt_state = load7;
    load7:
       if(in_hs)
         begin
           nxt_state = send7;
           push[7] = 1'b1;
         end
    send7:
      if(out_hs)
        nxt_state = load8;
    load8:
       if(in_hs)
         begin
           nxt_state = send8;
           push[8] = 1'b1;
         end
    send8:
      if(out_hs)
        nxt_state = load9;
    load9:
       if(in_hs)
         begin
           nxt_state = send9;
           push[9] = 1'b1;
         end
    send9:
      if(out_hs)
        nxt_state = load10;
    load10:
       if(in_hs)
         begin
           nxt_state = send10;
           push [10] = 1'b1;
         end
    send10:
      if(out_hs)
        if(pkt_zero)
          nxt_state = idle;
        else
          nxt_state = load_bypass;
    load_bypass:
       if(in_hs)
         nxt_state = send_bypass;
    wait_idle:
      if(out_hs)
        nxt_state = idle;
  endcase
end

rdyacpt #(8) in2wire (
  .upstream_rdy(pins.rdy_di),
  .upstream_acpt(pins.acpt_di),
  .upstream_data(pins.data_di),
  .downstream_rdy(in_rdy),
  .downstream_acpt(in_acpt),
  .downstream_data(input_down_data),
  .reset_n(pins.reset_n),
  .clk(pins.clk)
  );

count #(8) pkt_counter (
  .clk(pins.clk),
  .rst_n(pins.reset_n),
  .ld_n(pkt_ld_n),
  .up_dn(1'b0),
  .cen(pkt_cen),
  .din(8'hcb),
  .cnt_out(pkt_cnt),
  .zero(pkt_zero)
  );

fifo_shift_ram #(BUG) fifo (
  .clk(pins.clk),
  .reset_n(pins.reset_n),
  .push(push),
  .ram_re(ram_re),
  .din(input_down_data), 
  .sel(data_sel),
  .dout(fifo_data)
  );

rdyacpt #(8) out2wire (
  .upstream_rdy(out_rdy),
  .upstream_acpt(out_acpt),
  .upstream_data(do_reg),
  .downstream_rdy(pins.rdy_do),
  .downstream_acpt(pins.acpt_do),
  .downstream_data(pins.data_do),
  .reset_n(pins.reset_n),
  .clk(pins.clk)
  );

endmodule
