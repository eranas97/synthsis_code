module machine(d_in,valid_in,valid_out,d_out);
input [7:0]d_in;
input valid_in,valid_out;
output [15:0]d_out;
reg [7:0]B;
wire [7:0]A;
assign A[7:0]=d_in;
assign d_out[7:0]=valid_out?B:2'hZ;
assign d_out[15:8]=valid_out?A:2'hZ;

always@(valid_in)
begin
 B<=d_in;
end

endmodule 