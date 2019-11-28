`timescale 1ns/1ns

module ram2p_2kx8 (
  input wclk, we, re, rclk,
  input [7:0] din,
  input [10:0] waddr, raddr,
  output reg [7:0] dout
  );

reg [7:0] ram [0:2047];

always @(posedge rclk)
if(re)
  dout <= ram[raddr];
else
  dout <= dout;

always @(posedge wclk)
if(we)
  ram[waddr] <= din;

endmodule
