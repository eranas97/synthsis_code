`timescale 10ns/1ns
module tb_vedic3bit;
reg [2:0]A,B;
wire [5:0]mul;

vedic3bit M(A,B,mul);

initial
begin
    
    $dumpfile("vedicb.vcd");
    $dumpvars(0, tb_vedic3bit);

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