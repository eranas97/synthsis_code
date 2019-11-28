module tflip(t,clk,q);
input t,clk;
output reg q;
initial
begin
    q<=0;
end

always@(posedge clk)
begin
if(t==1)
    q<=~q;
else
q<=q;
end

endmodule