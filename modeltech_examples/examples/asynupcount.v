module asynupcount(t,clk,q);
input t,clk;
output [3:0]q;

tflip D0(t,clk,q[0]);
tflip D1(t,q[0],q[1]);
tflip D2(t,q[1],q[2]);
tflip D3(t,q[2],q[3]);
endmodule