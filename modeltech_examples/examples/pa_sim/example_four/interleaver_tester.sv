`timescale 1ns/1ns
import UPF::*;
module interleaver_tester;

    int CLK_PD1 = 12, CLK_PD2 = 18;
    int status;

    // DUT inputs & outputs
    reg reset_n, clock1, clock2;
    wire [15:0] q1, q2, q3, q4;
    reg [7:0] upstream_data;
    wire upstream_acpt;
    reg upstream_rdy = 0;
    reg [1:0] mem_select;

    // Power control signals
    reg mc_PWR, mc_SAVE, mc_RESTORE, mc_ISO, mc_CLK_GATE, sram_PWR;
    wire mc_PWR_ACK;

    // Device under test
    rtl_top dut (
        .clk1(clock1),
        .clk2(clock2),
        .reset_n(reset_n),
        .memsel(mem_select),
        .di_rdy(upstream_rdy),
        .di_acpt(upstream_acpt),
        .di_data(upstream_data),
        .mc_pwr(mc_PWR),
        .mc_pwr_ack(mc_PWR_ACK),
        .mc_save(mc_SAVE),
        .mc_restore(mc_RESTORE),
        .mc_iso(mc_ISO),
        .mc_clk_gate(mc_CLK_GATE),
        .sram_pwr(sram_PWR),
        .q1(q1),
        .q2(q2),
        .q3(q3),
        .q4(q4));


    // clock generator #1
    initial begin
        clock1 <= '0;
        forever #(CLK_PD1/2) clock1 = ~clock1;
    end

    // clock generator #2
    initial begin
        clock2 <= '0;
        #3 clock2 = '1;
        forever #(CLK_PD2/2) clock2 = ~clock2;
    end

    // Simulation control
    initial begin
        $timeformat(-9,0," ns", 8);
        reset_n = 1'b0;
        mem_select = 2'b01;
        {mc_PWR, mc_SAVE, mc_RESTORE, mc_ISO, mc_CLK_GATE} = 5'b10101;
        sram_PWR = 1'b0;
        $messagelog("%:S Initializing Supplies @%t", "note", $realtime);
        status = supply_on("/interleaver_tester/dut/VDD_0d99", 1.10);
        status = supply_on("/interleaver_tester/dut/VDD_0d81", 0.90);
        status = supply_on("/interleaver_tester/dut/VSS", 0);
        $messagelog("%:S Doing reset @%t", "note", $realtime);
        #100 reset_n = 1'b1;
        $messagelog("%:S Starting normal operation @%t", "note", $realtime);
        #52386;
        mem_select = 2'b00;
        //--------------------------------------------------------------------
        // Simulate decreased load - decrease voltage & lower clock frequency
        //     While we can change clock frequency in RTL, we cannot model
        //     different timing values until after synthesis.  This example
        //     does not show GLS simulation and DVFS.
        //--------------------------------------------------------------------
        CLK_PD1 = 30;
        #52387;
        //--------------------------------------------------------------------
        // Simulate increased load - increase voltage & raise clock freq
        //     While we can change clock frequency in RTL, we cannot model
        //     different timing values until after synthesis.  This example
        //     does not show GLS simulation and DVFS.
        //--------------------------------------------------------------------
        CLK_PD1 = 12;
        #42387;
        //--------------------------------------------------------------------
        // Power up & down the SRAM models
        //--------------------------------------------------------------------
        #5000 sram_PWR = 1'b1;
        $messagelog("%:S Powering down SRAM models @%t", "note", $realtime);
        #5000 sram_PWR = 1'b0;
        $messagelog("%:S Powering up SRAM models @%t", "note", $realtime);
        //--------------------------------------------------------------------
        // Normal power down on memory controller domain
        //--------------------------------------------------------------------
        #300 power_down_normal;
        //--------------------------------------------------------------------
        // Power down on memory controller domain without isolation
        //--------------------------------------------------------------------
        #5000 power_down_no_iso;
        //--------------------------------------------------------------------
        // Power down on memory controller domain without gating clock
        //--------------------------------------------------------------------
        #5000 power_down_no_clk_gate;
        //--------------------------------------------------------------------
        // Finish simulation
        //--------------------------------------------------------------------
        #10000 $messagelog("%:S Simulation finished @%t", "note", $realtime);
        $stop;
    end

    //-------------------------------------------------
    // Generate traffic for Interleaver
    //-------------------------------------------------
    int i = 0, j = 0;
    reg [31:0] up_rand_gen;

    always @(posedge clock1, negedge reset_n) begin
        if (!reset_n) begin
            upstream_rdy <= 1'b0;
            upstream_data <= 8'h00;
        end
        else begin
            if (upstream_rdy & upstream_acpt)
                upstream_rdy <= 0;
            if (!upstream_rdy) begin
                up_rand_gen = $random;
                if (up_rand_gen[3:0] >= 8) begin
                    upstream_rdy <= 1;
                    if (i == 0)
                        if (j == 0)
                            upstream_data <= 8'hb8;
                        else
                            upstream_data <= 8'h47;
                    else
                        upstream_data <= up_rand_gen[31:24];
                    if (i == 203) begin
                        i = 0;
                        if (j == 7)
                            j = 0;
                        else
                            j++;
                    end
                    else
                        i++;
                end
                else begin
                    upstream_rdy <= 0;
                    upstream_data <= 8'h00;
                end
            end
        end
    end

    //-------------------------------------------------
    // Verify correct output from interleaver
    //-------------------------------------------------
    reg [7:0] pipe_reg [0:1121];
    reg [7:0] expected_data;
    wire [7:0] cmp_fifo_data;

    reg  cmp_fifo_push;
    wire cmp_fifo_pop;

    int k, m;

    fifo #(.DEPTH(64),.SIZE(6),.WIDTH(8)) cmp_fifo (
        .clk(clock1),
        .reset_n(reset_n),
        .din(expected_data),
        .push(cmp_fifo_push),
        .pop(cmp_fifo_pop),
        .dout(cmp_fifo_data));

    assign cmp_fifo_pop = dut.i0.do_rdy & dut.i0.do_acpt;

    always @(posedge clock1, negedge reset_n) begin
        if (!reset_n) begin
            k = 0;
            cmp_fifo_push <= 1'b0;
        end
        else begin
            if (dut.i0.do_rdy & dut.i0.do_acpt)
                assert (cmp_fifo_data === dut.i0.do_data)
            else begin
                $display("CMP FIFO DATA = %h RTL MODEL DATA = %h",
                    cmp_fifo_data, dut.i0.do_data);
                $display("Data Miscompare ERROR at time", $time);
                $stop;
            end
            if (upstream_rdy & upstream_acpt) begin
                cmp_fifo_push <=  1'b1;
                case (k)
                    0: expected_data <= upstream_data;
                    1: begin
                        expected_data <= pipe_reg[16];
                        for (m = 16; m > 0; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[0] <= upstream_data;
                    end
                    2: begin
                        expected_data <= pipe_reg[50];
                        for (m = 50; m > 17; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[17] <= upstream_data;
                    end
                    3: begin
                        expected_data <= pipe_reg[101];
                        for (m = 101; m > 51; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[51] <= upstream_data;
                    end
                    4: begin
                        expected_data <= pipe_reg[169];
                        for (m = 169; m > 102; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[102] <= upstream_data;
                    end
                    5: begin
                        expected_data <= pipe_reg[254];
                        for (m = 254; m > 170; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[170] <= upstream_data;
                    end
                    6: begin
                        expected_data <= pipe_reg[356];
                        for (m = 356; m > 255; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[255] <= upstream_data;
                    end
                    7: begin
                        expected_data <= pipe_reg[475];
                        for (m = 475; m > 357; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[357] <= upstream_data;
                    end
                    8: begin
                        expected_data <= pipe_reg[611];
                        for (m = 611; m > 476; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[476] <= upstream_data;
                    end
                    9: begin
                        expected_data <= pipe_reg[764];
                        for (m = 764; m > 612; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[612] <= upstream_data;
                    end
                    10: begin
                        expected_data <= pipe_reg[934];
                        for (m = 934; m > 765; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[765] <= upstream_data;
                    end
                    11: begin
                        expected_data <= pipe_reg[1121];
                        for (m = 1121; m > 935; m--)
                            pipe_reg[m] <= pipe_reg[m-1];
                        pipe_reg[935] <= upstream_data;
                    end
                    default: begin
                        $display("Reached the Default case in ERROR at time",
                            $time);
                        $stop;
                    end
                endcase
                if (k == 11)
                    k = 0;
                else
                    ++k;
            end
            else begin
                cmp_fifo_push <= 1'b0;
            end
        end
    end

    //---------------------------------------------------------
    // Verify correct isolation values on ports of SRAM models
    //---------------------------------------------------------
/*
    property p_ceb_m1_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (dut.m1.CEB_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty
    property p_web_m1_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (dut.m1.WEB_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty
    property p_addr_m1_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (!dut.m1.A_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty

    a_ceb_m1_iso: assert property (p_ceb_m1_iso) else
        $error("%t: Invalid clamp value: m1 chip enable", $realtime);
    a_web_m1_iso: assert property (p_web_m1_iso) else
        $error("%t: Invalid clamp value: m1 write enable", $realtime);
    a_addr_m1_iso: assert property (p_addr_m1_iso) else
        $error("%t: Invalid clamp value: m1 addrss", $realtime);

    property p_ceb_m2_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (dut.m2.CEB_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty
    property p_web_m2_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (dut.m2.WEB_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty
    property p_addr_m2_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (!dut.m2.A_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty

    a_ceb_m2_iso: assert property (p_ceb_m2_iso) else
        $error("%t: Invalid clamp value: m2 chip enable", $realtime);
    a_web_m2_iso: assert property (p_web_m2_iso) else
        $error("%t: Invalid clamp value: m2 write enable", $realtime);
    a_addr_m2_iso: assert property (p_addr_m2_iso) else
        $error("%t: Invalid clamp value: m2 addrss", $realtime);

    property p_ceb_m3_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (dut.m3.CEB_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty
    property p_web_m3_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (dut.m3.WEB_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty
    property p_addr_m3_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (!dut.m3.A_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty

    a_ceb_m3_iso: assert property (p_ceb_m3_iso) else
        $error("%t: Invalid clamp value: m3 chip enable", $realtime);
    a_web_m3_iso: assert property (p_web_m3_iso) else
        $error("%t: Invalid clamp value: m3 write enable", $realtime);
    a_addr_m3_iso: assert property (p_addr_m3_iso) else
        $error("%t: Invalid clamp value: m3 addrss", $realtime);

    property p_ceb_m4_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (dut.m4.CEB_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty
    property p_web_m4_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (dut.m4.WEB_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty
    property p_addr_m4_iso;
        @(posedge clock2) $fell(mc_PWR) |-> (!dut.m4.A_i) throughout ##[0:$] $rose(mc_PWR);
    endproperty

    a_ceb_m4_iso: assert property (p_ceb_m4_iso) else
        $error("%t: Invalid clamp value: m4 chip enable", $realtime);
    a_web_m4_iso: assert property (p_web_m4_iso) else
        $error("%t: Invalid clamp value: m4 write enable", $realtime);
    a_addr_m4_iso: assert property (p_addr_m4_iso) else
        $error("%t: Invalid clamp value: m4 addrss", $realtime);

    property p_ret_clk_gate;
        @(negedge clock2) $rose(mc_SAVE) |-> ($stable(dut.mc0.clk) && (!dut.mc0.clk)) throughout ##[0:$] $fell(mc_RESTORE);
    endproperty

    a_ret_clk_gate: assert property (p_ret_clk_gate) else
        $error("%t: Clock not gated low during SAVE/RESTORE", $realtime);
*/
    //---------------------------------------------------------
    // Power control tasks
    //---------------------------------------------------------
    task power_down_normal;
        $messagelog("%:S Starting normal POWER DOWN cycle @%t", "note",
            $realtime);
        @(negedge clock2) mc_CLK_GATE = 1'b0;
        @(negedge clock2) mc_SAVE = 1'b1;
        @(negedge clock2) mc_SAVE = 1'b0;
        mc_ISO = 1'b1;
        #10 mc_PWR = 1'b0;
        #5000 mc_PWR = 1'b1;
        #5;
        @(negedge clock2) mc_RESTORE = 1'b0;
        @(negedge clock2) mc_RESTORE = 1'b1;
        #10 mc_CLK_GATE = 1'b1;
        mc_ISO = 1'b0;
        $messagelog("%:S Power restored @%t", "note", $realtime);
    endtask

    task power_down_no_iso;
        $messagelog("%:S Starting POWER DOWN without isolation @%t", "note",
            $realtime);
        @(negedge clock2) mc_CLK_GATE = 1'b0;
        @(negedge clock2) mc_SAVE = 1'b1;
        @(negedge clock2) mc_SAVE = 1'b0;
        #15 mc_PWR = 1'b0;
        #5000 mc_PWR = 1'b1;
        #5; 
        @(negedge clock2) mc_RESTORE = 1'b0;
        @(negedge clock2) mc_RESTORE = 1'b1;
        @(negedge clock2) mc_CLK_GATE = 1'b1;
        $messagelog("%:S Power restored @%t", "note", $realtime);
    endtask

    task power_down_no_clk_gate;
        $messagelog("%:S Starting POWER DOWN without clock gating @%t", "note",
            $realtime);
        @(negedge clock2) mc_SAVE = 1'b1;
        @(negedge clock2) mc_SAVE = 1'b0;
        #5 mc_ISO = 1'b1;
        #10 mc_PWR = 1'b0;
        #5000 mc_PWR = 1'b1;
        #5; 
        @(negedge clock2) mc_RESTORE = 1'b0;
        @(negedge clock2) mc_RESTORE = 1'b1;
        #10 mc_ISO = 1'b0;
        $messagelog("%:S Power restored @%t", "note", $realtime);
    endtask

endmodule
