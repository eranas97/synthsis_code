`timescale 1ns/1ns

module interleaver (
  input clk, reset_n, di_rdy, do_acpt, enable,
  input [7:0] di_data,
  output do_rdy, di_acpt,
  output [7:0] do_data);

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
  .tc(),
  .zero(pkt_zero)
  );

fifo_shift_ram fifo (
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
