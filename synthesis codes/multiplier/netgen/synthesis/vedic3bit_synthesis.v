////////////////////////////////////////////////////////////////////////////////
// Copyright (c) 1995-2013 Xilinx, Inc.  All rights reserved.
////////////////////////////////////////////////////////////////////////////////
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor: Xilinx
// \   \   \/     Version: P.20131013
//  \   \         Application: netgen
//  /   /         Filename: vedic3bit_synthesis.v
// /___/   /\     Timestamp: Thu Nov 28 23:59:28 2019
// \   \  /  \ 
//  \___\/\___\
//             
// Command	: -intstyle ise -insert_glbl true -w -dir netgen/synthesis -ofmt verilog -sim vedic3bit.ngc vedic3bit_synthesis.v 
// Device	: xc3s400-5-pq208
// Input file	: vedic3bit.ngc
// Output file	: D:\synthesis codes\multiplier\netgen\synthesis\vedic3bit_synthesis.v
// # of Modules	: 1
// Design Name	: vedic3bit
// Xilinx        : C:\Xilinx\14.7\ISE_DS\ISE\
//             
// Purpose:    
//     This verilog netlist is a verification model and uses simulation 
//     primitives which may not represent the true implementation of the 
//     device, however the netlist is functionally correct and should not 
//     be modified. This file cannot be synthesized and should only be used 
//     with supported simulation tools.
//             
// Reference:  
//     Command Line Tools User Guide, Chapter 23 and Synthesis and Simulation Design Guide, Chapter 6
//             
////////////////////////////////////////////////////////////////////////////////

`timescale 1 ns/1 ps

module vedic3bit (
mul, A, B
);
  output [5 : 0] mul;
  input [2 : 0] A;
  input [2 : 0] B;
  wire A_0_IBUF_3;
  wire A_1_IBUF_4;
  wire A_2_IBUF_5;
  wire B_0_IBUF_9;
  wire B_1_IBUF_10;
  wire B_2_IBUF_11;
  wire N18;
  wire N20;
  wire N21;
  wire N22;
  wire N23;
  wire N24;
  wire N25;
  wire N26;
  wire \P2/Mxor_sum_xo<0>40_20 ;
  wire \P2/Mxor_sum_xo<0>72 ;
  wire \P3/Mxor_sum_xo<0>20_22 ;
  wire \P3/Mxor_sum_xo<0>74_23 ;
  wire mul_0_OBUF_30;
  wire mul_1_OBUF_31;
  wire mul_2_OBUF_32;
  wire mul_3_OBUF_33;
  wire mul_4_OBUF_34;
  wire mul_5_OBUF_35;
  LUT4 #(
    .INIT ( 16'h8000 ))
  \P4/carry1  (
    .I0(B_2_IBUF_11),
    .I1(A_2_IBUF_5),
    .I2(B_1_IBUF_10),
    .I3(A_1_IBUF_4),
    .O(mul_5_OBUF_35)
  );
  LUT4 #(
    .INIT ( 16'h6AC0 ))
  \P0/Mxor_sum_Result1  (
    .I0(A_0_IBUF_3),
    .I1(B_0_IBUF_9),
    .I2(A_1_IBUF_4),
    .I3(B_1_IBUF_10),
    .O(mul_1_OBUF_31)
  );
  LUT2 #(
    .INIT ( 4'h8 ))
  \P3/Mxor_sum_xo<0>31  (
    .I0(B_0_IBUF_9),
    .I1(A_0_IBUF_3),
    .O(mul_0_OBUF_30)
  );
  LUT4 #(
    .INIT ( 16'h6444 ))
  \P3/Mxor_sum_xo<0>20  (
    .I0(A_0_IBUF_3),
    .I1(B_2_IBUF_11),
    .I2(B_0_IBUF_9),
    .I3(B_1_IBUF_10),
    .O(\P3/Mxor_sum_xo<0>20_22 )
  );
  LUT4 #(
    .INIT ( 16'hD9FF ))
  \P3/Mxor_sum_xo<0>74  (
    .I0(B_0_IBUF_9),
    .I1(B_2_IBUF_11),
    .I2(A_0_IBUF_3),
    .I3(A_1_IBUF_4),
    .O(\P3/Mxor_sum_xo<0>74_23 )
  );
  IBUF   A_2_IBUF (
    .I(A[2]),
    .O(A_2_IBUF_5)
  );
  IBUF   A_1_IBUF (
    .I(A[1]),
    .O(A_1_IBUF_4)
  );
  IBUF   A_0_IBUF (
    .I(A[0]),
    .O(A_0_IBUF_3)
  );
  IBUF   B_2_IBUF (
    .I(B[2]),
    .O(B_2_IBUF_11)
  );
  IBUF   B_1_IBUF (
    .I(B[1]),
    .O(B_1_IBUF_10)
  );
  IBUF   B_0_IBUF (
    .I(B[0]),
    .O(B_0_IBUF_9)
  );
  OBUF   mul_5_OBUF (
    .I(mul_5_OBUF_35),
    .O(mul[5])
  );
  OBUF   mul_4_OBUF (
    .I(mul_4_OBUF_34),
    .O(mul[4])
  );
  OBUF   mul_3_OBUF (
    .I(mul_3_OBUF_33),
    .O(mul[3])
  );
  OBUF   mul_2_OBUF (
    .I(mul_2_OBUF_32),
    .O(mul[2])
  );
  OBUF   mul_1_OBUF (
    .I(mul_1_OBUF_31),
    .O(mul[1])
  );
  OBUF   mul_0_OBUF (
    .I(mul_0_OBUF_30),
    .O(mul[0])
  );
  LUT3 #(
    .INIT ( 8'hD5 ))
  \P2/Mxor_sum_xo<0>68_SW0  (
    .I0(B_1_IBUF_10),
    .I1(A_0_IBUF_3),
    .I2(B_2_IBUF_11),
    .O(N18)
  );
  MUXF5   \P4/Mxor_sum_Result  (
    .I0(N20),
    .I1(N21),
    .S(B_2_IBUF_11),
    .O(mul_4_OBUF_34)
  );
  LUT4 #(
    .INIT ( 16'h8000 ))
  \P4/Mxor_sum_Result_F  (
    .I0(B_0_IBUF_9),
    .I1(B_1_IBUF_10),
    .I2(A_2_IBUF_5),
    .I3(A_1_IBUF_4),
    .O(N20)
  );
  LUT4 #(
    .INIT ( 16'h62AA ))
  \P4/Mxor_sum_Result_G  (
    .I0(A_2_IBUF_5),
    .I1(A_1_IBUF_4),
    .I2(A_0_IBUF_3),
    .I3(B_1_IBUF_10),
    .O(N21)
  );
  MUXF5   \P3/Mxor_sum_xo<0>87  (
    .I0(N22),
    .I1(N23),
    .S(A_2_IBUF_5),
    .O(mul_3_OBUF_33)
  );
  LUT4 #(
    .INIT ( 16'h8A88 ))
  \P3/Mxor_sum_xo<0>87_F  (
    .I0(A_1_IBUF_4),
    .I1(\P3/Mxor_sum_xo<0>20_22 ),
    .I2(B_1_IBUF_10),
    .I3(B_2_IBUF_11),
    .O(N22)
  );
  LUT4 #(
    .INIT ( 16'hF808 ))
  \P3/Mxor_sum_xo<0>87_G  (
    .I0(A_1_IBUF_4),
    .I1(B_2_IBUF_11),
    .I2(B_1_IBUF_10),
    .I3(\P3/Mxor_sum_xo<0>74_23 ),
    .O(N23)
  );
  MUXF5   \P2/Mxor_sum_xo<0>40  (
    .I0(N24),
    .I1(N25),
    .S(A_0_IBUF_3),
    .O(\P2/Mxor_sum_xo<0>40_20 )
  );
  LUT4 #(
    .INIT ( 16'h0888 ))
  \P2/Mxor_sum_xo<0>40_F  (
    .I0(A_1_IBUF_4),
    .I1(B_1_IBUF_10),
    .I2(A_2_IBUF_5),
    .I3(B_0_IBUF_9),
    .O(N24)
  );
  LUT4 #(
    .INIT ( 16'h2A6A ))
  \P2/Mxor_sum_xo<0>40_G  (
    .I0(B_2_IBUF_11),
    .I1(A_1_IBUF_4),
    .I2(B_1_IBUF_10),
    .I3(B_0_IBUF_9),
    .O(N25)
  );
  VCC   XST_VCC (
    .P(N26)
  );
  LUT4 #(
    .INIT ( 16'h8088 ))
  \P2/Mxor_sum_xo<0>721  (
    .I0(B_0_IBUF_9),
    .I1(A_2_IBUF_5),
    .I2(N18),
    .I3(A_1_IBUF_4),
    .O(\P2/Mxor_sum_xo<0>72 )
  );
  MUXF5   \P2/Mxor_sum_xo<0>72_f5  (
    .I0(\P2/Mxor_sum_xo<0>72 ),
    .I1(N26),
    .S(\P2/Mxor_sum_xo<0>40_20 ),
    .O(mul_2_OBUF_32)
  );
endmodule


`ifndef GLBL
`define GLBL

`timescale  1 ps / 1 ps

module glbl ();

    parameter ROC_WIDTH = 100000;
    parameter TOC_WIDTH = 0;

//--------   STARTUP Globals --------------
    wire GSR;
    wire GTS;
    wire GWE;
    wire PRLD;
    tri1 p_up_tmp;
    tri (weak1, strong0) PLL_LOCKG = p_up_tmp;

    wire PROGB_GLBL;
    wire CCLKO_GLBL;

    reg GSR_int;
    reg GTS_int;
    reg PRLD_int;

//--------   JTAG Globals --------------
    wire JTAG_TDO_GLBL;
    wire JTAG_TCK_GLBL;
    wire JTAG_TDI_GLBL;
    wire JTAG_TMS_GLBL;
    wire JTAG_TRST_GLBL;

    reg JTAG_CAPTURE_GLBL;
    reg JTAG_RESET_GLBL;
    reg JTAG_SHIFT_GLBL;
    reg JTAG_UPDATE_GLBL;
    reg JTAG_RUNTEST_GLBL;

    reg JTAG_SEL1_GLBL = 0;
    reg JTAG_SEL2_GLBL = 0 ;
    reg JTAG_SEL3_GLBL = 0;
    reg JTAG_SEL4_GLBL = 0;

    reg JTAG_USER_TDO1_GLBL = 1'bz;
    reg JTAG_USER_TDO2_GLBL = 1'bz;
    reg JTAG_USER_TDO3_GLBL = 1'bz;
    reg JTAG_USER_TDO4_GLBL = 1'bz;

    assign (weak1, weak0) GSR = GSR_int;
    assign (weak1, weak0) GTS = GTS_int;
    assign (weak1, weak0) PRLD = PRLD_int;

    initial begin
	GSR_int = 1'b1;
	PRLD_int = 1'b1;
	#(ROC_WIDTH)
	GSR_int = 1'b0;
	PRLD_int = 1'b0;
    end

    initial begin
	GTS_int = 1'b1;
	#(TOC_WIDTH)
	GTS_int = 1'b0;
    end

endmodule

`endif

