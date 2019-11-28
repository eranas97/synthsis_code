module dflipusingmux(D,clk,Q);
input D,clk;
output Q;
wire a,b;
assign b=~clk;
mux21 M1(a,D,clk,a);
mux21 M2(Q,a,b,Q);
endmodule