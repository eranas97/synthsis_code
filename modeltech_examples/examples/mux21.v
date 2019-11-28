module mux21(I0,I1,S,Y);
input I0,I1;
input S;
output Y;
assign Y=(S)?I1:I0;
endmodule