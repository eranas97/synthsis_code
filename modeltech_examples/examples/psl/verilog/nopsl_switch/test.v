/****************************************************/
// Module: tb
/****************************************************/
module tb;
reg clk;
reg b0, b1, b2, b3;

initial clk = 0;
always #50 clk = ~clk;

/*
   psl begin
    default clock = (posedge clk);
    A_E:assert always {b0} |=> b1;
    always @(posedge clk)
        $display($time, " TEST : posedge clk.");
   end
 */

initial
begin
		 b0 = 0;   b1 = 0;   b2 = 0;   b3 = 0;
#100     b0 = 1;   b1 = 0;   b2 = 0;   b3 = 0; //100
#100     b0 = 0;   b1 = 1;   b2 = 0;   b3 = 0; //200
#100     b0 = 1;   b1 = 1;   b2 = 1;   b3 = 0; //300
#100     b0 = 0;   b1 = 0;   b2 = 1;   b3 = 0; //400
#1500    $finish;
end

endmodule

