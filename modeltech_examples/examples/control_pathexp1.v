module control_pathexp1(d_in,clk,start,done,finish,ldO,ldA,ldB,op_code); //ports declared
input clk,start,done;
input [15:0]d_in;
input [1:0]op_code; //input ports
output reg finish,ldA,ldB,ldO; //output ports
reg [3:0]state; //defining state variale register
parameter s0=0000,s1=0001,s2=0010,s3=0011,s4=0100,s5=0101,s6=0110,s7=0111,s8=1000; // states as parameters

always@(posedge clk) // always block for state change only
begin
  case(state) //case statement
     s0:begin
         if(start==1)
         state<=s1;
         else
         state<=s0;
       end
     s1:state<=s2;
     s2:state<=s3;
     s3:begin
          if(op_code==01)
          state<=s4; 
          else if(op_code==10)
          state<=s5; 
          else if(op_code==11)
          state<=s6;
          else if(op_code==00)
          state<=s7;
        end
     s4:state<=s8;
     s5:state<=s8;
     s6:state<=s8;
     s7:state<=s8;
     default:state<=s0;
  endcase
end

always@(posedge clk) // always block for signal genrations for datapath state values
begin
  case(state) // case statement
  s0:begin finish<=0;ldA<=0;ldB<=0; end
  s1:begin ldA<=1;ldB<=0; end
  s2:begin ldA=0;ldB<=1; end
  s3:begin ldA<=0;ldB=0;ldO<=1; end
  s4:begin ldA<=1;ldB<=0;ldO<=0; end
  s5:begin ldA<=1;ldB<=0;ldO<=0; end
  s6:begin ldA<=1;ldB<=0;ldO<=0; end
  s7:begin ldA<=1;ldB<=0;ldO<=0; end
  s8:begin
     ldA<=0;
     ldB<=0;
     ldO<=0;
     if(done)
     finish=1;
    end
    default:begin finish<=0;ldA<=0;ldB<=0; end
  endcase
end
endmodule