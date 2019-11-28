`timescale 1ns/100ps
module adder_test;
reg a,b,c;
wire c0,opt; 
adder g(a,b,c,c0,opt);
initial
begin
a=0;b=0;c=0;
end
always #20a=~a;
always #10b=~b;
always #5c=~c;
initial
begin
 $dumpvars(0);
 #40
 $finish;
end
endmodule