`timescale 100ps/10ps
module testforencoder83;
reg [0:7]D;
reg enable;
wire [0:2]Q;

encoderusingcasez D1(D,Y);

initial
begin
     enable=1;
    D=00000001;
end

always #2 D=D+1; 

endmodule