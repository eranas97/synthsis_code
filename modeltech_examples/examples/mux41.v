module mux41(I,S,Y);
input [0:3]I;
input [0:1]S;
output Y;
wire a,b;
mux21 M1(I[0],I[1],S[0],a);
mux21 M2(I[2],I[3],S[0],b);
mux21 M3(a,b,S[1],Y);
endmodule