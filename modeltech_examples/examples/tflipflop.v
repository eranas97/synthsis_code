module tflipflop(t,clk,q);
input clk,t;
output reg q;
always@(posedge clk);
begin
if(t==1)
q=~q;
else
q=q;
end
endmodule
