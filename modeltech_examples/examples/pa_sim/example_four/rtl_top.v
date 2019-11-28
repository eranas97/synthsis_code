`timescale 1ns/1ns

module rtl_top (
    input clk1, clk2, reset_n, di_rdy,
    input mc_pwr, mc_save, mc_restore, mc_iso, mc_clk_gate, sram_pwr,
    input [1:0] memsel,
    input [7:0] di_data,
    output di_acpt, mc_pwr_ack,
    output [15:0] q1, q2, q3, q4);

    wire do_rdy_out, do_acpt_out, do_rdy, do_acpt;
    wire [3:0] ceb, web, ceb_uniso, web_unshift;
    wire [7:0] do_data, address;
    wire [15:0] data_bus;

    //-----------------------------------------------
    // insert PAD cells for all inputs & outputs
    //-----------------------------------------------

    // intermediate signals for PADS
    wire di_rdy_c, clk1_c, clk2_c, reset_n_c;
    wire mc_pwr_c, mc_save_c, mc_restore_c, mc_iso_c, mc_clk_gate_c;
    wire sram_pwr_c;
    wire [1:0] memsel_c;
    wire [7:0] di_data_c;
    wire di_acpt_i, mc_pwr_ack_i;
    wire [15:0] q1_i, q2_i, q3_i, q4_i;

    // single bit inputs
    PAD_IN pi0 (.PAD(clk1), .C(clk1_c));
    PAD_IN pi1 (.PAD(clk2), .C(clk2_c));
    PAD_IN pi2 (.PAD(reset_n), .C(reset_n_c));
    PAD_IN pi3 (.PAD(di_rdy), .C(di_rdy_c));
    PAD_IN pi4 (.PAD(mc_pwr), .C(mc_pwr_c));
    PAD_IN pi5 (.PAD(mc_save), .C(mc_save_c));
    PAD_IN pi6 (.PAD(mc_restore), .C(mc_restore_c));
    PAD_IN pi7 (.PAD(mc_iso), .C(mc_iso_c));
    PAD_IN pi8 (.PAD(mc_clk_gate), .C(mc_clk_gate_c));
    PAD_IN pi9 (.PAD(sram_pwr), .C(sram_pwr_c));

    // multiple bit inputs
    PAD_IN pi_10 (.PAD(memsel[0]), .C(memsel_c[0]));
    PAD_IN pi_11 (.PAD(memsel[1]), .C(memsel_c[1]));
    generate
        genvar var0;
        for (var0 = 0; var0 < 8; var0 = var0 + 1)
        begin:di_data_slice
            PAD_IN pi_12 (.PAD(di_data[var0]), .C(di_data_c[var0]));
        end
    endgenerate

    // single bit outputs
    PAD_OUT po0 (.I(di_acpt_i), .PAD(di_acpt));
    PAD_OUT po1 (.I(mc_pwr_ack_i), .PAD(mc_pwr_ack));

    // multiple bit outputs
    generate
        genvar var1;
        for (var1 = 0; var1 < 16; var1 = var1 + 1)
        begin:q1_slice
            PAD_OUT po2 (.I(q1_i[var1]), .PAD(q1[var1]));
        end
    endgenerate
    generate
        genvar var2;
        for (var2 = 0; var2 < 16; var2 = var2 + 1)
        begin:q2_slice
            PAD_OUT po3 (.I(q2_i[var2]), .PAD(q2[var2]));
        end
    endgenerate
    generate
        genvar var3;
        for (var3 = 0; var3 < 16; var3 = var3 + 1)
        begin:q3_slice
            PAD_OUT po4 (.I(q3_i[var3]), .PAD(q3[var3]));
        end
    endgenerate
    generate
        genvar var4;
        for (var4 = 0; var4 < 16; var4 = var4 + 1)
        begin:q4_slice
            PAD_OUT po5 (.I(q4_i[var4]), .PAD(q4[var4]));
        end
    endgenerate

    // Interleaver
    interleaver i0 (
        .clk(clk1_c),
        .reset_n(reset_n_c),
        .di_rdy(di_rdy_c),
        .do_acpt(do_acpt_out),
        .enable(1'b1),
        .di_data(di_data_c),
        .do_rdy(do_rdy),
        .di_acpt(di_acpt_i),
        .do_data(do_data));

    // zero fill upper 8 bits to make bus width 16
    assign data_bus = {{8{1'b0}}, do_data};

    // Asynchronous bridge for handshake signals between the interleaver
    // and the memory controller
    async_bridge i1 (
        .clk1(clk1_c),
        .clk2(clk2_c),
        .rstn(reset_n_c),
        .do_acpt_in(do_acpt),
        .do_acpt_out(do_acpt_out),
        .do_rdy_in(do_rdy),
        .do_rdy_out(do_rdy_out));

    // gate the memory controller clock low during power down
    wire clk2_gate;
    and an0 (clk2_gate, mc_clk_gate_c, clk2_c); 

    // Memory controller
    mem_ctrl mc0 (
        .clk(clk2_gate),
        .rstn(reset_n_c),
        .memsel(memsel_c),
        .do_rdy(do_rdy_out),
        .do_acpt(do_acpt),
        .mc_pwr(mc_pwr_c),
        .mc_pwr_ack(mc_pwr_ack_i),
        .mc_save(mc_save_c),
        .mc_restore(mc_restore_c),
        .ceb(ceb_uniso),
        .web(web_unshift),
        .addr(address));

ISOCELL ceb_iso_0 (
	.I(ceb_uniso[0]),
	.ISO(mc_iso_c),
	.Z(ceb[0]));
	
ISOCELL ceb_iso_1 (
	.I(ceb_uniso[1]),
	.ISO(mc_iso_c),
	.Z(ceb[1]));

ISOCELL ceb_iso_2 (
	.I(ceb_uniso[2]),
	.ISO(mc_iso_c),
	.Z(ceb[2]));

ISOCELL ceb_iso_3 (
	.I(ceb_uniso[3]),
	.ISO(mc_iso_c),
	.Z(ceb[3]));

LSCELL web_ls_0 (
	.I(web_unshift[0]),
	.Z(web[0]));
	
LSCELL web_ls_1 (
	.I(web_unshift[1]),
	.Z(web[1]));

LSCELL web_ls_2 (
	.I(web_unshift[2]),
	.Z(web[2]));

LSCELL web_ls_3 (
	.I(web_unshift[3]),
	.Z(web[3]));

    // SRAM #1
    sram_256x16 m1 (
        .PD(sram_pwr_c),
        .CLK(clk2_c),
        .CEB(ceb[0]),
        .WEB(web[0]),
        .RSTB(reset_n_c),
        .A(address),
        .D(data_bus),
        .Q(q1_i));

    // SRAM #2
    sram_256x16 m2 (
        .PD(sram_pwr_c),
        .CLK(clk2_c),
        .CEB(ceb[1]),
        .WEB(web[1]),
        .RSTB(reset_n_c),
        .A(address),
        .D(data_bus),
        .Q(q2_i));

    // SRAM #3
    sram_256x16 m3 (
        .PD(sram_pwr_c),
        .CLK(clk2_c),
        .CEB(ceb[2]),
        .WEB(web[2]),
        .RSTB(reset_n_c),
        .A(address),
        .D(data_bus),
        .Q(q3_i));

    // SRAM #4
    sram_256x16 m4 (
        .PD(sram_pwr_c),
        .CLK(clk2_c),
        .CEB(ceb[3]),
        .WEB(web[3]),
        .RSTB(reset_n_c),
        .A(address),
        .D(data_bus),
        .Q(q4_i));

endmodule
