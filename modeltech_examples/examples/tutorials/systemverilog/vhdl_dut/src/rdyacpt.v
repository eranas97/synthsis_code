module rdyacpt #(parameter WIDTH = 8) (
  input clk, reset_n, upstream_rdy, downstream_acpt,
  input [WIDTH-1:0] upstream_data,
  output downstream_rdy, upstream_acpt,
  output [WIDTH-1:0] downstream_data);


  wire en_v0, en_v1, v0_sel;
  reg v0, v1, ready_reg;
  reg [WIDTH-1:0] d0, d1;

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
      v0 <=  1'b0;
      v1 <=  1'b0;
    end
  else
    begin
      ready_reg <=  downstream_acpt | ~v0;
      if (en_v0)
        if (v0_sel)
          begin
            v0 <=  v1;
            d0 <=  d1;
          end
        else
          begin
            v0 <=  upstream_rdy;
            d0 <=  upstream_data;
          end
      if (en_v1)
        begin
          v1 <=  upstream_rdy;
          d1 <=  upstream_data;
        end
    end
/*
always @(posedge clk)
  begin
    ready_reg <=  downstream_acpt | ~v0;
    if (en_v0)
      if(v0_sel)
        d0 <=  d1;
      else
        d0 <=  upstream_data;
    if (en_v1)
       d1 <=  upstream_data;
  end
*/

endmodule
