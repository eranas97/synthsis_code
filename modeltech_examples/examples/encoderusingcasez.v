module encoderusingcasez(D,Y);
input [7:0]D; 
output reg [2:0]Y;

always@(*)
begin
    casez(D)
    8'b10000000:Y=3'b111;
    8'bz1000000:Y=3'b110;
    8'bzz100000:Y=3'b101;
    8'bzzz10000:Y=3'b100;
    8'bzzzz1000:Y=3'b011;
    8'bzzzzz100:Y=3'b010;
    8'bzzzzzz10:Y=3'b001;
    8'bzzzzzzz1:Y=3'b000;
    default:Y=3'b000;
    endcase
end

endmodule