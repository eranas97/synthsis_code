
module dusingsr(d,clk,q,q_bar);
input d,clk;
output q,q_bar;
wire d_bar;
assign d_bar=~d;
srflipflop F1(d,d_bar,clk,q,q_bar);
endmodule