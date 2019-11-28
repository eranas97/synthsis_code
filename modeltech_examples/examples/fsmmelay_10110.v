module fsmmelay_10110(in,out,clk,rst);
input in,clk,rst;
output reg out;
parameter A=3'b000,B=3'b001,C=3'b010,D=3'b011,E=3'b100;
reg [2:0]p_state,n_state;

always@(posedge clk,posedge rst)
begin
 if(rst)
 begin
      n_state<=A;
     p_state<=n_state;
      out<=1'b0; 
 end

  else
       p_state<=n_state;
end

always@(p_state)
begin 
    case(p_state)
     A:begin
      if(in)
       begin  
        n_state<=B;
        p_state<=n_state;
        out<=1'b0;
       end
      else
       begin  
        n_state<=A;
        p_state<=n_state;
        out<=1'b0;
       end
      end


     B:begin
      if(in)
       begin  
        n_state<=B;
        p_state<=n_state;
        out<=1'b0;
       end
      else
       begin  
        n_state<=C;
        p_state<=n_state;
        out<=1'b0;
       end
      end


     C:begin
      if(in)
       begin  
        n_state<=D;
        p_state<=n_state;
        out<=1'b0;
       end
      else
       begin  
        n_state<=A;
        p_state<=n_state;
        out<=1'b0;
       end
      end


     D:begin
      if(in)
       begin  
        n_state<=E;
        p_state<=n_state;
        out<=1'b0;
       end
      else
       begin  
        n_state<=C;
        p_state<=n_state;
        out<=1'b0;
       end
      end


     E:begin
      if(in)
       begin  
        n_state<=B;
        p_state<=n_state;
        out<=1'b0;
       end
      else
       begin  
        n_state<=C;
        p_state<=n_state;
        out<=1'b1;
       end
      end


     default: begin
      n_state<=A;
      p_state<=n_state;
        out<=1'b0;
      end


    endcase
end

endmodule