`timescale 1ns/1ns

module rtl_top (
	input clk, reset,
	input [3:0] in1, in2,
	input [1:0] sel,
	output [3:0] out1,
	input IN_PWR,ALU_PWR_low,ALU_PWR_moderate,ALU_PWR_high,OUT_PWR,IN_ISO_PWR, OUT_RET_PWR,IN_ISO, OUT_RET);

	//-----------------------------------------------
	// insert PAD cells for all inputs & outputs
	//-----------------------------------------------

	// intermediate signals for PADS
	wire clk_c, reset_c;
	wire [3:0] in1_c,in2_c;
	wire [1:0] sel_c;
	wire [3:0] out1_i;

	// single bit inputs
	PAD_IN pi0 (.PAD(clk), .C(clk_c));
	PAD_IN pi1 (.PAD(reset), .C(reset_c));

	// multiple bit inputs
	PAD_IN pi_10 (.PAD(in1[0]), .C(in1_c[0]));
	PAD_IN pi_11 (.PAD(in1[1]), .C(in1_c[1]));
	PAD_IN pi_12 (.PAD(in1[2]), .C(in1_c[2]));
	PAD_IN pi_13 (.PAD(in1[3]), .C(in1_c[3]));

	PAD_IN pi_20 (.PAD(in2[0]), .C(in2_c[0]));
	PAD_IN pi_21 (.PAD(in2[1]), .C(in2_c[1]));
	PAD_IN pi_22 (.PAD(in2[2]), .C(in2_c[2]));
	PAD_IN pi_23 (.PAD(in2[3]), .C(in2_c[3]));

	PAD_IN pi_30 (.PAD(sel[0]), .C(sel_c[0]));
	PAD_IN pi_31 (.PAD(sel[1]), .C(sel_c[1]));

	// multiple bit output
	PAD_OUT po_10 (.I(out1_i[0]), .PAD(out1[0]));
	PAD_OUT po_11 (.I(out1_i[1]), .PAD(out1[1]));
	PAD_OUT po_12 (.I(out1_i[2]), .PAD(out1[2]));
	PAD_OUT po_13 (.I(out1_i[3]), .PAD(out1[3]));

	//-----------------------------------------------
	// insert RTL components
	//-----------------------------------------------

	// intermediate signals for instances
	wire [3:0] in1_del,in2_del,out_alu;
	wire [1:0] sel_del;
	
	// register for in1
	register #(.N(4)) in1_reg (.clk (clk_c),
	.reset (reset),
	.d (in1_c),
	.q (in1_del)); 

	// register for in2
	register #(.N(4)) in2_reg (.clk (clk_c),
	.reset (reset),
	.d (in2_c),
	.q (in2_del));

	// register for sel
	register #(.N(2)) sel_reg (.clk (clk_c),
	.reset (reset),
	.d (sel_c),
	.q (sel_del));

	// alu
	alu alu_inst (.in1(in1_del),
	.in2(in2_del),
	.sel(sel_del),
	.out1(out_alu));

	// register for out1 
	register #(.N(4)) out1_reg (.clk (clk_c),
	.reset (reset),
	.d (out_alu),
	.q (out1_i));


endmodule
