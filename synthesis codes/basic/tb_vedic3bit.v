`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date:    20:25:04 08/27/2019 
// Design Name: 
// Module Name:    tb_vedic3bit 
// Project Name: 
// Target Devices: 
// Tool versions: 
// Description: 
//
// Dependencies: 
//
// Revision: 
// Revision 0.01 - File Created
// Additional Comments: 
//
//////////////////////////////////////////////////////////////////////////////////
`timescale 10ns/1ns //timescale defined 
module tb_vedic3bit;
reg [2:0]A,B; //ports declared
wire [5:0]mul;

vedic3bit M(A,B,mul);// module instantiation

initial //various test inputs
begin
    A=3'b001;
    B=3'b010;

    #1 A=3'b010;
       B=3'b100;

    #1A=3'b100;
      B=3'b101;

    #1 A=3'b101;
       B=3'b110;

    #1A=3'b110;
      B=3'b111;
end

endmodule
