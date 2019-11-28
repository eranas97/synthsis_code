module fulladder(a,b,cout,s);
input a,b;
output s,cout;
assign s=a^b;
assign cout=a&b;
endmodule