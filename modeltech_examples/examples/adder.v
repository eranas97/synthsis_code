module adder(a,b,c,co,opt);
input a;
input b;
input c;
output wire co, opt;
assign opt=a^b^c;
assign co=((a*b)|(b*c)|(c*a));
endmodule