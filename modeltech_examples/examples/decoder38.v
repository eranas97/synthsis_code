module decoder38(I,Y);
input [0:2]I;
output [0:7]Y;
assign Y[0]=~I[0]&~I[1]&~I[2];
assign Y[1]=~I[0]&~I[1]&I[2];
assign Y[2]=~I[0]&I[1]&~I[2];
assign Y[3]=~I[0]&I[1]&I[2];
assign Y[4]=I[0]&~I[1]&~I[2];
assign Y[5]=I[0]&~I[1]&I[2];
assign Y[6]=I[0]&I[1]&~I[2];
assign Y[7]=I[0]&I[1]&~I[2];
endmodule