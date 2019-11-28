`timescale 1ns/1ns
module test_exp1;
reg clk,start;
reg [15:0]d_in;
reg [1:0]op_code;
wire finish,ldA,ldB,ldO,done;

control_pathexp1 dut2 (d_in,clk,start,done,finish,ldO,ldA,ldB,op_code);
datapathexp1 dut1 (ldA,ldB,ldO,clk,d_in,op_code,done);

always #5 clk=~clk;

initial
begin
 clk=0;
 d_in=16'b0000000000000000;
 op_code=2'b00;
 start=0;
 done=0;
 finish=0;
 ldO=0;
 ldA=0;
 ldB=0;
end

initial
begin
 #5 start=1, d_in=16'b0000000000000011, op_code=2'b00; 
  #10  d_in=16'b0000000000000001;

   #10 start=1, d_in=16'b0000000000000011, op_code=2'b01; 
  #10  d_in=16'b0000000000000001;

   #10 start=1, d_in=16'b0000000000000011, op_code=2'b10; 
  #10  d_in=16'b0000000000000001;

   #10 start=1, d_in=16'b0000000000000011, op_code=2'b11; 
  #10  d_in=16'b0000000000000001;
end

initial
begin
 $dumpvars(0);
 #40
 $finish;
end

endmodule
