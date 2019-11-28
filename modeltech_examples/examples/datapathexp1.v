module data_pathexp1(ldA,ldB,ldO,clk,d_in,op_code,done); //module declaration and ports declared
input ldA,ldB,ldO,clk;
input [1:0]op_code;
input [15:0]d_in; // input ports
output reg done; // output ports
reg [15:0]A; // defining accumulator
reg [15:0]B,C,O; // defining registers
wire [15:0] a,b,c,d; // intermediate wires

always@(posedge clk) // always block for loading registers
begin
   if(ldA)
   A<=d_in;
   else if (ldB)
   B<=d_in;
   else if (ldO)
   O<=d_in;
end

always@(posedge clk) // always block for computation logic
begin
       if(op_code==01)
    begin
     if(ldA)
      A<=A+B;
    done<=1;
    end

    else if(op_code==10)
    begin
     if(ldA)
      A<=A-B;
    done<=1;
    end

    else if(op_code==11)
    begin
     if(ldA)
      A<=A*B;
    done<=1;
    end

    else if(op_code==00)
    begin
     if(ldA)
      A<=A/B;
    done<=1;
    end
end
endmodule // module ended