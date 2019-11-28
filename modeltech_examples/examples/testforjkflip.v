`timescale 100ps/10ps
module testforjkflip;
reg clk,j,k;
wire q,q_bar;

jkflip F1(j,k,clk,q,q_bar);

initial
begin
    clk=0;
    j=0;k=0;
    #2 j=0;k=1;
     #2 j=1;k=0;
      #2 j=1;k=1;
    #8 $stop;
    $monitor($time," clk=%b j=%b k=%b q=%b q_bar=%b",clk,j,k,q,q_bar);
end

always #2 clk=~clk;

endmodule