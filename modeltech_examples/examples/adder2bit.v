module adder2bit(A,B,sum,carry);
input A,B;
output sum;
output carry;
assign sum=A^B;
assign carry=A&B;
endmodule