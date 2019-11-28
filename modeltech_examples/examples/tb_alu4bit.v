`timescale 10ns/1ns
module tb_alu4bit;
reg [3:0]A,B;
reg [1:0]op_code;
wire [7:0]out;

alu4bit A1(A,B,op_code,out);

initial
begin
 A=4'b0000; //addition
 B=4'b0001;
 op_code=2'b00;

#1 A=4'b0001;//subtraction
 B=4'b0001;
 op_code=2'b01;  

#1 A=4'b0001;  //increment
 op_code=2'b10;

#1 A=4'b0001; //dicrement
 op_code=2'b11; 
end

endmodule