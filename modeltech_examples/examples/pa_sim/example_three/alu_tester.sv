`timescale 1ns/1ns
import UPF::*;
module alu_tester;

	int status;
	int CLK_PD1 = 12;

	// DUT inputs & outputs
	reg clk, reset;
	wire [3:0] out1;
	reg [3:0] in1,in2;
	reg [1:0] sel;

	// Power control signals
	reg IN_PWR,MUX_PWR;

	// Device under test
	rtl_top dut (
	.clk(clk),
	.reset(reset),
	.in1(in1),
	.in2(in2),
	.sel(sel),
	.out1(out1),
	.IN_PWR(IN_PWR),
	.MUX_PWR(MUX_PWR));

	// clock generator #1
	initial begin
		clk <= '0;
		forever #(CLK_PD1/2) clk = ~clk;
	end

	// Simulation control
	initial begin
		$timeformat(-9,0," ns", 8);
		reset = 1'b0;
		IN_PWR = 1'b1;
		MUX_PWR = 1'b1;
		$messagelog("%:S Initializing Supplies @%t", "note", $realtime);
		status = supply_on("/alu_tester/dut/MAIN_PWR", 5.0);
		status = supply_on("/alu_tester/dut/MAIN_GND", 0.0);
		$messagelog("%:S Doing reset @%t", "note", $realtime);
		reset = 1'b1;
		#100;
		in1 = 4'b0101;
		in2 = 4'b1100;
		sel = 2'b00;
		#100;
		$messagelog("%:S Starting normal operation @%t", "note", $realtime);
		reset = 1'b0;
		//--------------------------------------------------------------------
		// Changing the arthematic operations
		//--------------------------------------------------------------------
		#100;
		sel = 2'b01;
		#100;
		sel = 2'b10;
		#100;
		sel = 2'b11;
		#100;
		//--------------------------------------------------------------------
		// Shutting down IN_PWR
		//--------------------------------------------------------------------
		#200 shut_down_IN_PWR;
		//--------------------------------------------------------------------
		// Shutting down MUX_PWR
		//--------------------------------------------------------------------
		#200 shut_down_MUX_PWR;
		//--------------------------------------------------------------------
		// Finish simulation
		//--------------------------------------------------------------------
		#1000 $messagelog("%:S Simulation finished @%t", "note", $realtime);
		$stop;
	end

	task shut_down_IN_PWR;
		$messagelog("%:S Starting shutting down IN_PWR @%t", "note",$realtime);
		IN_PWR = 1'b0;
		#100;
		$messagelog("%:S PIN_PWR restored @%t", "note", $realtime);
		IN_PWR = 1'b1;
	endtask

	task shut_down_MUX_PWR;
		$messagelog("%:S Starting shutting down MUX_PWR @%t", "note",$realtime);
		MUX_PWR = 1'b0;
		#100;
		$messagelog("%:S MUX_PWR restored @%t", "note", $realtime);
		MUX_PWR = 1'b1;
	endtask

endmodule
