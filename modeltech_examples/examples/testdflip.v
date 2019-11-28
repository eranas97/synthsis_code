`timescale 100ps/10ps
module testdflip();
reg d,clk;
wire q;

dflip D1(d,clk,q);

initial
begin
d=0;
clk=0;
$monitor($time,"clk=%d and d=%d",clk,d);
end

always #5 clk=~clk;
always #4 d=~d;

endmodule