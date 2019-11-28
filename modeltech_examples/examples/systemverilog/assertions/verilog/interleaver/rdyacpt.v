module rdyacpt #(parameter WIDTH = 8) (
  input clk, reset_n, upstream_rdy, downstream_acpt,
  input [WIDTH-1:0] upstream_data,
  output downstream_rdy, upstream_acpt,
  output [WIDTH-1:0] downstream_data);

//`define CLK2Q #2
`define CLK2Q

  wire en_v0, en_v1, v0_sel;
  //wire downstream_acpt;
  reg v0, v1, ready_reg;
  reg [WIDTH-1:0] d0, d1;
  //wire [WIDTH-1:0] downstream_data;

assign #1
  en_v0 = ~v0 | downstream_acpt,
  en_v1 = ~v1 | ready_reg,
  v0_sel = en_v0  & v1 & ~ready_reg,
  upstream_acpt = ~v1 | ready_reg,
  downstream_rdy = v0,
  downstream_data = d0;

always @(posedge clk or negedge reset_n)
  if (!reset_n)
    begin
      v0 <= `CLK2Q 1'b0;
      v1 <= `CLK2Q 1'b0;
      d0 <= `CLK2Q 1'b0;
      d1 <= `CLK2Q 1'b0;
      ready_reg <= `CLK2Q downstream_acpt | ~v0;
    end
  else
    begin
      ready_reg <= `CLK2Q downstream_acpt | ~v0;
      if (en_v0)
        if (v0_sel)
        begin
          v0 <= `CLK2Q v1;
          d0 <= `CLK2Q d1;
        end
        else begin
          v0 <= `CLK2Q upstream_rdy;
          d0 <= `CLK2Q upstream_data;
        end
      if (en_v1)
        begin
        v1 <= `CLK2Q upstream_rdy;
        d1 <= `CLK2Q upstream_data;
        end
    end

endmodule
