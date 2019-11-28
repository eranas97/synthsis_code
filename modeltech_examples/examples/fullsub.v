module fullsub(bin,a,b,bout,d);
input a,b,bin;
output d,bout;
assign d=(~a&~b&bin)|(a&~b&~bin)|(a&b&bin);
assign bout=(~a&bin)|(~a&b)|(b&bin);
endmodule