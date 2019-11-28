module encoder83(I,Y);
output [0:2]Y;
input [0:7]I;
assign Y[0]=I[0]|I[1]|I[2]|I[3];
assign Y[1]=I[0]|I[1]|I[4]|I[5];
assign Y[2]=I[0]|I[4]|I[2]|I[6];
endmodule