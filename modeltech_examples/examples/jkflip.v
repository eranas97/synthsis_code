module jkflip(j,k,clk,q,q_bar);
input j,k,clk;
output reg q,q_bar;
always@(posedge clk)
begin
    case({j,k})
    {1'b0,1'b0}:begin q=q;q_bar=~q; end
    {1'b0,1'b1}:begin q=0;q_bar=~q; end
    {1'b1,1'b0}:begin q=1;q_bar=~q; end
    {1'b1,1'b1}:begin q=~q;q_bar=~q_bar; end
    endcase
end
endmodule