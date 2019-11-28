`ifdef USE_SV
//typedef enum bit [4:0] {idle, send_bypass, load0, send0, load1, send1, load2,
typedef enum {idle, send_bypass, load0, send0, load1, send1, load2,
                    send2, load3, send3, load4, send4, load5, send5, load6,
                    send6, load7, send7, load8, send8, load9, send9, load10,
                    send10, load_bypass, wait_idle
                   } fsm_state;
`endif

module interleaver #(parameter BUG=0) (
  input clk, reset_n, di_rdy, do_acpt, enable,
  input [7:0] di_data,
  output do_rdy, di_acpt,
  output [7:0] do_data
  );

`ifdef USE_SV
  fsm_state nxt_state, int_state;
`else
  reg [4:0] nxt_state, int_state;
  parameter idle        = 5'b00000,
            send_bypass = 5'b00001,
            load0       = 5'b00010,
            send0       = 5'b00011,
            load1       = 5'b00100,
            send1       = 5'b00101,
            load2       = 5'b00110,
            send2       = 5'b00111,
            load3       = 5'b01000,
            send3       = 5'b01001,
            load4       = 5'b01010,
            send4       = 5'b01011,
            load5       = 5'b01100,
            send5       = 5'b01101,
            load6       = 5'b01110,
            send6       = 5'b01111,
            load7       = 5'b10000,
            send7       = 5'b10001,
            load8       = 5'b10010,
            send8       = 5'b10011,
            load9       = 5'b10100,
            send9       = 5'b10101,
            load10      = 5'b10110,
            send10      = 5'b10111,
            load_bypass = 5'b11000,
            wait_idle   = 5'b11001;
`endif

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
property sync_bypass_check;
@(posedge clk) (int_state == idle && in_hs) |-> (sync_in_valid |=>
               (int_state == send_bypass && out_hs && (do_reg == 8'h47 || do_reg == 8'hb8))[=1]);
endproperty

assert property(sync_bypass_check);

// detect valid states machine transitions
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
/*
    bins load0_bin = {load0};
    bins send0_bin = {send0};
    bins load1_bin = {load1};
    bins send1_bin = {send1};
    bins load2_bin = {load2};
    bins send2_bin = {send2};
    bins load3_bin = {load3};
    bins send3_bin = {send3};
    bins load4_bin = {load4};
    bins send4_bin = {send4};
    bins load5_bin = {load5};
    bins send5_bin = {send5};
    bins load6_bin = {load6};
    bins send6_bin = {send6};
    bins load7_bin = {load7};
    bins send7_bin = {send7};
    bins load8_bin = {load8};
    bins send8_bin = {send8};
    bins load9_bin = {load9};
    bins send9_bin = {send9};
    bins load10_bin = {load10};
    bins send10_bin = {send10};
*/
  }
  coverpoint in_hs;
  coverpoint out_hs;

  in_hsXint_state: cross in_hs, int_state;
  out_hsXint_state: cross out_hs, int_state;
  //option.comment = "covered it";

endgroup

sm_cvg sm_cvg_c1 = new;

//always
// #10000 $display("Coverage = %f", sm_cvg_c1.get_coverage());

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
                   

  pkt_cen  = reset_n & in_hs & ~pkt_zero,
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

always @(posedge clk)
if(in_hs && (int_state == idle || int_state == load_bypass))
  do_reg <= input_down_data;
else if(|push)
  do_reg <= fifo_data;
else
  do_reg <= do_reg;
       
always @(posedge clk or negedge reset_n)
if(!reset_n)
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
  .upstream_rdy(di_rdy),
  .upstream_acpt(di_acpt),
  .upstream_data(di_data),
  .downstream_rdy(in_rdy),
  .downstream_acpt(in_acpt),
  .downstream_data(input_down_data),
  .reset_n(reset_n),
  .clk(clk)
  );

count #(8) pkt_counter (
  .clk(clk),
  .rst_n(reset_n),
  .ld_n(pkt_ld_n),
  .up_dn(1'b0),
  .cen(pkt_cen),
  .din(8'hcb),
  .cnt_out(pkt_cnt),
  .zero(pkt_zero)
  );

fifo_shift_ram #(BUG) fifo (
  .clk(clk),
  .reset_n(reset_n),
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
  .downstream_rdy(do_rdy),
  .downstream_acpt(do_acpt),
  .downstream_data(do_data),
  .reset_n(reset_n),
  .clk(clk)
  );

endmodule
