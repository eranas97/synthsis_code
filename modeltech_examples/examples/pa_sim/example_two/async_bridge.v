module async_bridge (
    input clk1, clk2, rstn, do_rdy_in, do_acpt_in,
    output reg do_acpt_out, do_rdy_out);

    reg do_acpt, do_rdy, do_rdy_in_d1, do_rdy_in_d2;
    reg ready_tmp, acpt_tmp1, acpt_tmp2, acpt_tmp3;

    // synchronizer for data ready signal
    always @(posedge clk1 or negedge rstn) begin
        if (rstn == 1'b0) begin
            do_rdy_in_d1 <= 1'b0;
            do_rdy_in_d2 <= 1'b0;
        end
        else begin
            do_rdy_in_d1 <= do_rdy_in;
            do_rdy_in_d2 <= do_rdy_in_d1;
        end
    end

    always @(posedge clk1 or negedge rstn) begin
        if (rstn == 1'b0)
            do_rdy <= 1'b0;
        else if ( do_rdy_in_d1 != do_rdy_in_d2 )
            do_rdy <= do_rdy_in_d1;
        else
            do_rdy <= do_rdy_in;
    end

    always @(posedge clk2 or negedge rstn) begin
        if (rstn == 1'b0) begin
            ready_tmp <= 1'b0;
            do_rdy_out <= 1'b0;
            do_acpt <= 1'b0;
        end
        else begin
            ready_tmp <= do_rdy;
            do_rdy_out <= ready_tmp;
            do_acpt <= do_acpt_in;
        end
    end

    // synchronizer and pulse generator for data accept signal
    always @(posedge clk1 or negedge rstn) begin
        if (rstn == 1'b0) begin
            acpt_tmp1 <= 1'b0;
            acpt_tmp2 <= 1'b0;
            acpt_tmp3 <= 1'b0;
        end
        else begin
            acpt_tmp1 <= do_acpt;
            acpt_tmp2 <= acpt_tmp1;
            acpt_tmp3 <= acpt_tmp2;
        end
    end

    // data accept output logic for one clock pulse generation
    always @*
        do_acpt_out = acpt_tmp2 & ~acpt_tmp3;

endmodule
