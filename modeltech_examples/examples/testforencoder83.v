`timescale 100ps/10ps
module testforencoder83;
reg [7:0]D;
wire [2:0]Q;

encoderusingcasez D1(D,Y);

initial
begin
    D=8'b00000000;
    #2 D=8'b10000000;
    #2 D=8'bz1000000;
    #2 D=8'bzz100000;
    #2 D=8'bzzz10000;
    #2 D=8'bzzzz1000;
    #2 D=8'bzzzzz100;
    #2 D=8'bzzzzzz10;
    #2 D=8'bzzzzzzz1;
end
endmodule
