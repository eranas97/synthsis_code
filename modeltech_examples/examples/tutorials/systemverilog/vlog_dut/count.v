module count #(parameter WIDTH = 8) (
  input clk, rst_n, ld_n, up_dn, cen,
  input [WIDTH-1:0] din,
  output tc, zero,
  output reg [WIDTH-1:0] cnt_out
  );

assign
  tc    = cnt_out == {WIDTH{1'b1}},
  zero  = cnt_out == {WIDTH{1'b0}};

always @(posedge clk or negedge rst_n)
if (!rst_n)
  cnt_out <= {WIDTH{1'b0}};
else
  if (!ld_n)
    cnt_out <= din;
  else if (!cen)
    cnt_out <= cnt_out;
  else
    case (up_dn)
      1'b1: cnt_out <= cnt_out + 1;
      1'b0: cnt_out <= cnt_out - 1;
    endcase

endmodule
