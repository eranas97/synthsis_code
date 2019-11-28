`timescale 100ps/10ps
module testforfsm;
reg in,clk,rst;
wire out;

fsmmelay_10110 F1(in,out,clk,rst);

initial
begin
    clk=0;
    rst=1;
    in=0;
    
    #0.75 in=1;
    #1 in=0;
    #1.5 in=1;
    #3 in=1;
    #0.75 in=0;
end

initial
begin
#0.5 rst=0;
end

always #1 clk=~clk;

endmodule