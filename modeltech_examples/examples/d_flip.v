module d_flip(q reset clk d);

input clk,reset,d;

output q;

always@(posedge clk);

begin
   
 if (reset)
    
 q<=0;
    
 else
    
 q<=d; 

end

endmodule