module comp2bit(a,b,G,L,E);
input [0:1]a;
input [0:1]b;
output G,L,E;
assign E=a[0]^a[1]^b[0]^b[1];

assign G=(~b[1]&a[1])|(~b[0]&~b[1]&a[0])|(a[1]&a[0]&~b[0]);

assign L=(~a[1]&~b[1])|(~a[1]&~a[0]&b[0])|(b[1]&b[0]&~a[0]);
endmodule
