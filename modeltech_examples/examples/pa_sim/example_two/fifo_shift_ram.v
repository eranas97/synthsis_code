`timescale 1ns/1ns

module fifo_shift_ram (
  input clk, reset_n, ram_re,
  input [10:0] push,
  input [7:0] din,
  input [3:0] sel,
  output [7:0] dout
  );

wire [10:0] addra;
wire [10:0] addrb;
reg [10:0] waddr[1:11];
reg [10:0] raddr[1:11];
wire ram_we;


assign
  ram_we = |push ? 1'b1 : 1'b0;

// write address mux
assign
  addra = (sel == 4'h0) ? waddr[1] :
          (sel == 4'h1) ? waddr[2] :
          (sel == 4'h2) ? waddr[3] :
          (sel == 4'h3) ? waddr[4] :
          (sel == 4'h4) ? waddr[5] :
          (sel == 4'h5) ? waddr[6] :
          (sel == 4'h6) ? waddr[7] :
          (sel == 4'h7) ? waddr[8] :
          (sel == 4'h8) ? waddr[9] :
          (sel == 4'h9) ? waddr[10] : waddr[11];

// read address mux
assign
  addrb = (sel == 4'h0) ? raddr[1] :
          (sel == 4'h1) ? raddr[2] :
          (sel == 4'h2) ? raddr[3] :
          (sel == 4'h3) ? raddr[4] :
          (sel == 4'h4) ? raddr[5] :
          (sel == 4'h5) ? raddr[6] :
          (sel == 4'h6) ? raddr[7] :
          (sel == 4'h7) ? raddr[8] :
          (sel == 4'h8) ? raddr[9] :
          (sel == 4'h9) ? raddr[10] : raddr[11];

// increment the write address pointers if they are selected
// and there is a write to the ram. Check for max address
// before incrementing. If max address is reached then reset
// address to initial value.

always @(posedge clk or negedge reset_n)
if (!reset_n)
  begin
    waddr[1]  <= 11'd0;
    waddr[2]  <= 11'd64;
    waddr[3]  <= 11'd128;
    waddr[4]  <= 11'd256;
    waddr[5]  <= 11'd384;
    waddr[6]  <= 11'd512;
    waddr[7]  <= 11'd640;
    waddr[8]  <= 11'd768;
    waddr[9]  <= 11'd1024;
    waddr[10] <= 11'd1280;
    waddr[11] <= 11'd1536;
  end
else if (|push)
  case (sel)
    4'h0:
      if (waddr[1] == 11'd16)
        waddr[1] <= 11'd0;
      else
        waddr[1] <= waddr[1] + 11'd1;
    4'h1:
      if (waddr[2] == 11'd97)
        waddr[2] <= 11'd64;
      else
        waddr[2] <= waddr[2] + 11'd1;
    4'h2:
      if (waddr[3] == 11'd178)
        waddr[3] <= 11'd128;
      else
        waddr[3] <= waddr[3] + 11'd1;
    4'h3:
      if (waddr[4] == 11'd323)
        waddr[4] <= 11'd256;
      else
        waddr[4] <= waddr[4] + 11'd1;
    4'h4:
      if (waddr[5] == 11'd468)
        waddr[5] <= 11'd384;
      else
        waddr[5] <= waddr[5] + 11'd1;
    4'h5:
      if (waddr[6] == 11'd613)
        waddr[6] <= 11'd512;
      else
        waddr[6] <= waddr[6] + 11'd1;
    4'h6:
      if (waddr[7] == 11'd758)
        waddr[7] <= 11'd640;
      else
        waddr[7] <= waddr[7] + 11'd1;
    4'h7:
      if (waddr[8] == 11'd903)
        waddr[8] <= 11'd768;
      else
        waddr[8] <= waddr[8] + 11'd1;
    4'h8:
      if (waddr[9] == 11'd1176)
        waddr[9] <= 11'd1024;
      else
        waddr[9] <= waddr[9] + 11'd1;
    4'h9:
      if (waddr[10] == 11'd1449)
        waddr[10] <= 11'd1280;
      else
        waddr[10] <= waddr[10] + 11'd1;
    default:
        if (waddr[11] == 11'd1722)
          waddr[11] <= 11'd1536;
        else
          waddr[11] <= waddr[11] + 11'd1;
  endcase

// the read address pointers needs to increment each
// time the write pointers are incremented. The ram read
// are initialized to the write address plus 1. Check for
// the max address before incrementing. If max address is
// reached then reset address to initial value.

always @(posedge clk or negedge reset_n)
if (!reset_n)
  begin
    raddr[1]  <= 11'd0;
    raddr[2]  <= 11'd64;
    raddr[3]  <= 11'd128;
    raddr[4]  <= 11'd256;
    raddr[5]  <= 11'd384;
    raddr[6]  <= 11'd512;
    raddr[7]  <= 11'd640;
    raddr[8]  <= 11'd768;
    raddr[9]  <= 11'd1024;
    raddr[10] <= 11'd1280;
    raddr[11] <= 11'd1536;
  end
else if (|push)
  case (sel)
    4'h0:
      if (raddr[1] == 11'd16)
        raddr[1] <= 11'd0;
      else
        raddr[1] <= raddr[1] + 11'd1;
    4'h1:
      if (raddr[2] == 11'd97)
        raddr[2] <= 11'd64;
      else
        raddr[2] <= raddr[2] + 11'd1;
    4'h2:
      if (raddr[3] == 11'd178)
        raddr[3] <= 11'd128;
      else
        raddr[3] <= raddr[3] + 11'd1;
    4'h3:
      if (raddr[4] == 11'd323)
        raddr[4] <= 11'd256;
      else
        raddr[4] <= raddr[4] + 11'd1;
    4'h4:
      if (raddr[5] == 11'd468)
        raddr[5] <= 11'd384;
      else
        raddr[5] <= raddr[5] + 11'd1;
    4'h5:
      if (raddr[6] == 11'd613)
        raddr[6] <= 11'd512;
      else
        raddr[6] <= raddr[6] + 11'd1;
    4'h6:
      if (raddr[7] == 11'd758)
        raddr[7] <= 11'd640;
      else
        raddr[7] <= raddr[7] + 11'd1;
    4'h7:
      if (raddr[8] == 11'd903)
        raddr[8] <= 11'd768;
      else
        raddr[8] <= raddr[8] + 11'd1;
    4'h8:
      if (raddr[9] == 11'd1176)
        raddr[9] <= 11'd1024;
      else
        raddr[9] <= raddr[9] + 11'd1;
    4'h9:
      if (raddr[10] == 11'd1449)
        raddr[10] <= 11'd1280;
      else
        raddr[10] <= raddr[10] + 11'd1;
    default:
        if (raddr[11] == 11'd1722)
          raddr[11] <= 11'd1536;
        else
          raddr[11] <= raddr[11] + 11'd1;
  endcase

ram2p_2kx8 ram_block (
  .wclk(clk),
  .din(din),
  .waddr(addra),
  .we(ram_we),
  .re(ram_re),
  .rclk(clk),
  .raddr(addrb),
  .dout(dout)
  );

endmodule
