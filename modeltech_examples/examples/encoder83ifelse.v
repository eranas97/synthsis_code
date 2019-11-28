module encoder83ifelse(D,enable,Q);
input [0:7]D;
input enable;
output reg [0:2]Q;

always@(*)
begin
    if(D[0]==1)
    Q=3'b000;

    else if(D[1]==1)
    Q=3'b001;

   else if(D[2]==1)
    Q=3'b010;

   else if(D[3]==1)
    Q=3'b011;

   else if(D[4]==1)
    Q=3'b100;

    else if(D[5]==1)
    Q=3'b101;

    else if(D[6]==1)
    Q=3'b110;

   else if(D[7]==1)
    Q=3'b111;

    else
    Q=3'bX;

end

endmodule