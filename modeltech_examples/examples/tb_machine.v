`timescale 10ns/1ns
module tb_machine;
reg [7:0]d_in ;
reg valid_in,valid_out;
wire [15:0]d_out;

machine M(d_in,valid_in,valid_out,d_out);

initial
begin
    valid_in=0;
    valid_out=0;
    d_in=8'b10101010;
    #1 valid_in=1;
    #1 valid_in=0;
    #1 valid_out=1;
    #2 valid_out=0;
    #5 $stop;
end

endmodule