`timescale 100ps/10ps
module testforasynupcount;
reg t,clk;
wire [0:3]q;

asynupcount C1(t,clk,q);

initial
begin
clk=0;
t=1;
#40 $stop;
end

always #1 clk=~clk;

endmodule