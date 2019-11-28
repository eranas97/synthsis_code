module ripplecarryadder4(input [0:3]a,b,input cin,output cout,output [0:3]s);
wire [0:2]c;
fulladder A0(a[0],b[0],cin,c[0],s[0]);
fulladder A1(a[1],b[1],c[0],c[1],s[1]);
fulladder A2(a[2],b[2],c[1],c[2],s[2]);
fulladder A3(a[3],b[3],c[2],cout,s[3]);
endmodule