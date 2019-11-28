module adder3bit(A,B,C,sum,carry);
input A,B,C;
output sum;
output carry;
assign sum=A^B^C;
assign carry=(A&B)|(B&C)|(C&A);
endmodule