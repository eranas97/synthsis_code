`timescale 1ns/1ns
import UPF::*;
module alu_tester;

	int status;
	int CLK_PD1 = 12;

	// DUT inputs & outputs
	reg clk, reset, window;
	wire clk_window;
	wire [3:0] out1;
	reg [3:0] in1,in2;
	reg [1:0] sel;

	// Power control signals
	reg IN_PWR,ALU_PWR_low,ALU_PWR_moderate,ALU_PWR_high,OUT_PWR;
	reg IN_ISO, OUT_RET;
	reg IN_ISO_PWR, OUT_RET_PWR;

	// Device under test
	rtl_top dut (
	.clk(clk_window),
	.reset(reset),
	.in1(in1),
	.in2(in2),
	.sel(sel),
	.out1(out1),
	.IN_PWR(IN_PWR),
	.ALU_PWR_low(ALU_PWR_low),
	.ALU_PWR_moderate(ALU_PWR_moderate),
	.ALU_PWR_high(ALU_PWR_high),
	.OUT_PWR(OUT_PWR),
	.IN_ISO_PWR(IN_ISO_PWR),
	.OUT_RET_PWR(OUT_RET_PWR),
	.IN_ISO(IN_ISO),
	.OUT_RET(OUT_RET));

	// clock generator #1
	initial begin
		clk <= '0;
		forever #(CLK_PD1/2) clk = ~clk;
	end

	assign clk_window = clk & window;

	// Simulation control
	initial begin
		$timeformat(-9,0," ns", 8);
		window = 1'b1;
		reset = 1'b0;
		IN_PWR = 1'b1;
		ALU_PWR_low = 1'b1;
		ALU_PWR_moderate = 1'b0;
		ALU_PWR_high = 1'b0;
		OUT_PWR = 1'b0;
		IN_ISO = 1'b0;
		OUT_RET = 1'b0;
		IN_ISO_PWR = 1'b1;
		OUT_RET_PWR = 1'b1;
		$messagelog("%:S Initializing Supplies @%t", "note", $realtime);
		status = supply_on("/alu_tester/dut/MAIN_PWR_high", 7.0);
		status = supply_on("/alu_tester/dut/MAIN_PWR_moderate", 5.0);
		status = supply_on("/alu_tester/dut/MAIN_PWR_low", 3.0);
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
		// Shutting down the PD_IN power domain
		//--------------------------------------------------------------------
		#200 shut_down_PD_IN;
		//--------------------------------------------------------------------
		// Shutting down the PD_ALU power domain
		//--------------------------------------------------------------------
		#200 shut_down_PD_ALU;
		//--------------------------------------------------------------------
		// Shutting down the PD_OUT power domain
		//--------------------------------------------------------------------
		#200 shut_down_PD_OUT;
		//--------------------------------------------------------------------
		// Starting isolation scenario for PD_IN power domain
		//--------------------------------------------------------------------
		#200 PD_IN_ISO_task;
		//--------------------------------------------------------------------
		// Starting retention scenario for PD_OUT power domain
		//--------------------------------------------------------------------
		#200 PD_OUT_RET_task;
		//--------------------------------------------------------------------
		// Starting working on moderate voltage for PD_ALU power domain
		//--------------------------------------------------------------------
		#200 PD_ALU_moderate_volt_task;
		//--------------------------------------------------------------------
		// Starting working on high voltage for PD_ALU power domain
		//--------------------------------------------------------------------
		#200 PD_ALU_high_volt_task;
		//--------------------------------------------------------------------
		// Starting working on low voltage for PD_ALU power domain
		//--------------------------------------------------------------------
		#200 PD_ALU_low_volt_task;
		//--------------------------------------------------------------------
		// Finish simulation
		//--------------------------------------------------------------------
		#1000 $messagelog("%:S Simulation finished @%t", "note", $realtime);
		$stop;
	end

	task shut_down_PD_IN;
		$messagelog("%:S Starting shutting down PD_IN power domain @%t", "note",$realtime);
		IN_PWR = 1'b0;
		#100;
		IN_PWR = 1'b1;
		$messagelog("%:S Primary power restored @%t", "note", $realtime);
	endtask

	task shut_down_PD_ALU;
		$messagelog("%:S Starting shutting down PD_ALU power domain @%t", "note",$realtime);
		ALU_PWR_low = 1'b0;
		ALU_PWR_high = 1'b0;
		ALU_PWR_moderate = 1'b0;
		#100;
		ALU_PWR_low = 1'b1;
		ALU_PWR_high = 1'b0;
		ALU_PWR_moderate = 1'b0;
		$messagelog("%:S Primary power restored @%t", "note", $realtime);
	endtask

	task shut_down_PD_OUT;
		$messagelog("%:S Starting shutting down PD_OUT power domain @%t", "note",$realtime);
		OUT_PWR = 1'b0;
		#100;
		OUT_PWR = 1'b1;
		$messagelog("%:S Primary power restored @%t", "note", $realtime);
	endtask

	task PD_IN_ISO_task;
		$messagelog("%:S Starting isolation scenario for PD_IN power domain @%t", "note",$realtime);
		IN_ISO = 1'b1;
		#20;
		IN_PWR = 1'b0;
		#100;
		IN_PWR = 1'b1;
		#20;
		IN_ISO = 1'b0;
		$messagelog("%:S Ending the isolation scenario @%t", "note", $realtime);
	endtask

	task PD_OUT_RET_task;
		$messagelog("%:S Starting retention scenario for PD_OUT power domain @%t", "note",$realtime);
		window = 1'b0;
		#20;
		OUT_RET = 1'b1;
		#20;
		OUT_PWR = 1'b0;
		#100;
		OUT_PWR = 1'b1;
		#20;
		OUT_RET = 1'b0;
		#20;
		window = 1'b1;
		$messagelog("%:S Ending the retention scenario @%t", "note", $realtime);
	endtask

	task PD_ALU_low_volt_task;
		$messagelog("%:S Starting working on low voltage for PD_ALU power domain @%t", "note",$realtime);
		ALU_PWR_low = 1'b1;
		ALU_PWR_high = 1'b0;
		ALU_PWR_moderate = 1'b0;
	endtask

	task PD_ALU_high_volt_task;
		$messagelog("%:S Starting working on high voltage for PD_ALU power domain @%t", "note",$realtime);
		ALU_PWR_low = 1'b0;
		ALU_PWR_high = 1'b1;
		ALU_PWR_moderate = 1'b0;
	endtask

	task PD_ALU_moderate_volt_task;
		$messagelog("%:S Starting working on moderate voltage for PD_ALU power domain @%t", "note",$realtime);
		ALU_PWR_low = 1'b0;
		ALU_PWR_high = 1'b0;
		ALU_PWR_moderate = 1'b1;
	endtask

endmodule
