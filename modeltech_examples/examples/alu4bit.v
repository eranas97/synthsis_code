module alu4bit(A,B,op_code,out);
input[3:0]A,B;
input[1:0]op_code;
output reg [7:0]out;

always@(op_code,A,B)
begin
    case(op_code)
    2'b00:out<=(A+B);
    2'b01:out<=(A-B);
    2'b10:out<=(A+1);
    2'b11:out<=(A-1);
    default:out<=8'bZ;
    endcase
end

endmodule
