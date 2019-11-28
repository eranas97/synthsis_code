`timescale 1ns/1ns

module fifo #(parameter DEPTH=256, SIZE=8, WIDTH=8) (
  input clk, reset_n, push, pop,
  input [WIDTH-1:0] din,
  output [WIDTH-1:0] dout
  );

reg [WIDTH-1:0] ram [0:DEPTH-1];
reg [SIZE-1:0] waddr, raddr;

assign
  dout = ram[raddr];

always @(posedge clk or negedge reset_n)
if (!reset_n)
  begin
    waddr <= {WIDTH{1'b0}};
    raddr <= {WIDTH{1'b0}};
  end
else
  begin
    if(push)
      begin
        ram[waddr] <= din;
        waddr <= waddr + 1;
      end
    if(pop)
      raddr <= raddr + 1;
  end

endmodule

