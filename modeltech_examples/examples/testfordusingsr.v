`timescale 100ps/10ps
module testfordusingsr;
reg d,clk;
wire q,q_bar;

dusingsr D1(d,clk,q,q_bar);

initial 
begin
    d=0;
    clk=0;
    #40 $stop;
end

always #5 clk=~clk;
always #4 d=~d;

endmodule