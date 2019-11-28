
module srflipflop(s,r,clk,q,q_bar);
input s,r,clk;
output reg q,q_bar;
always@(posedge clk)
begin
if(s==0)
begin
    if(r==0)
    q=q;
    q_bar=~q;
    if(r==1)
    q=0;
    q_bar=~q;
end 
if(s==1)
begin
    if(r==0)
    q=1;
    q_bar=~q;
    if(r==1)
    q=1'bx;
    q_bar=1'bx;
end
end
endmodule