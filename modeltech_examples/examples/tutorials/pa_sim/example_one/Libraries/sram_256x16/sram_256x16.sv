`timescale 1ns/1ps
`celldefine
module sram_256x16 (
    input PD, CLK, CEB, WEB, RSTB,
    input [7:0] A,
    input [15:0] D,
    output [15:0] Q);

    // Create internally buffered versions of the ports
    wire PD_i, CLK_i, CEB_i, WEB_i, RSTB_i;
    wire [7:0] A_i;
    wire [15:0] D_i;
    wire [15:0] Q_i;

    buf (PD_i, PD);
    buf (CLK_i, CLK);
    buf (CEB_i, CEB);
    buf (WEB_i, WEB);
    buf (RSTB_i, RSTB);
    buf addr_array [7:0] (A_i[7:0], A[7:0]);
    buf data_array [15:0] (D_i[15:0], D[15:0]);
    buf output_array [15:0] (Q[15:0], Q_i[15:0]);

    // Internal signals and arrays
    reg [15:0] MEMORY[63:0][3:0];
    reg [15:0] Q_tmp;

    wire iCEB = PD_i ? 1'b1 : CEB_i;
    wire [5:0] ROW_i = A_i[7:2];
    wire [1:0] COL_i = A_i[1:0];

    assign Q_i = PD_i ? 16'h0000 : Q_tmp;

    // Read/Write logic
    always @(posedge CLK_i, negedge RSTB_i) begin
        if (RSTB_i === 1'b0) begin
            for (int row = 0; row <= 63; ++row)
                for (int col = 0; col <= 3; ++col)
                    MEMORY[row][col] = '0;
        end
        else if (iCEB === 1'b0) begin
            //------------------------------------------
            // READ cycle
            //------------------------------------------
            if (WEB_i === 1'b1) begin
                if ( ^A_i === 1'bx ) begin
                    //$messagelog("%:S Addr UNKNOWN during read @%0t",
                    //    "Warning", $time);
                    Q_tmp = 'x;
                    for (int row = 0; row <= 63; ++row)
                        for (int col = 0; col <= 3; ++col)
                            MEMORY[row][col] = 'x;
                end
                else begin
                    Q_tmp = MEMORY[ROW_i][COL_i];
                end
            end
            //------------------------------------------
            // WRITE cycle
            //------------------------------------------
            else if (WEB_i === 1'b0) begin
                if ( ^A_i === 1'bx ) begin
                    //$messagelog("%:S Addr UNKNOWN during write @%0t",
                    //    "Warning", $time);
                    for (int row = 0; row <= 63; ++row)
                        for (int col = 0; col <= 3; ++col)
                            MEMORY[row][col] = 'x;
                end
                else begin
                    MEMORY[ROW_i][COL_i] = D_i;
                end
            end
            else begin
                //$messagelog("%:S Read/Write enable signal UNKNOWN @%0t",
                //    "Warning", $time);
                if ( ^A_i === 1'bx ) begin
                    Q_tmp = {16{1'bx}};
                    for (int row = 0; row <= 63; ++row)
                        for (int col = 0; col <= 3; ++col)
                            MEMORY[row][col] = 'x;
                end
                else begin
                    Q_tmp = 'x;
                    MEMORY[ROW_i][COL_i] = 'x;
                end
            end
        end
        else if (iCEB === 1'b1) begin
            if (PD===1'b1) begin
               Q_tmp = 'x;
            end
        end
        else begin
            //$messagelog("%:S Chip enable signal UNKNOWN @%0t",
            //    "Warning", $time);
            Q_tmp = 'x;
            for (int row = 0; row <= 63; ++row)
                for (int col = 0; col <= 3; ++col)
                    MEMORY[row][col] = 'x;
        end
    end

    // check for unknown values on power control signal
    always @(PD_i) begin
        if (PD_i === 1'bx || PD_i === 1'bz) begin
            //$messagelog("%:S Power control signal UNKNOWN @%0t",
            //    "Warning", $time);
            Q_tmp = 'x;
            for (int row = 0; row <= 63; ++row)
                for (int col = 0; col <= 3; ++col)
                    MEMORY[row][col] = 'x;
        end
    end

    // check for unknown values on the clock but only when chip enable active
    always @(CLK_i) begin
        if (CLK_i === 1'bx || CLK_i === 1'bz) begin
            if (iCEB === 1'b0) begin
                //$messagelog("%:S Clock UNKNOWN while chip enable active @%0t",
                //    "Warning", $time);
                Q_tmp = 'x;
                for (int row = 0; row <= 63; ++row)
                    for (int col = 0; col <= 3; ++col)
                        MEMORY[row][col] = 'x;
            end
        end
    end

    specify
        specparam t_rise = 1:2:3, t_fall = 1:2:3;
        if (!PD) (posedge CLK => (Q[0] : D[0])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[1] : D[1])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[2] : D[2])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[3] : D[3])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[4] : D[4])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[5] : D[5])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[6] : D[6])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[7] : D[7])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[8] : D[8])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[9] : D[9])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[10] : D[10])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[11] : D[11])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[12] : D[12])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[13] : D[13])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[14] : D[14])) = (t_rise, t_fall);
        if (!PD) (posedge CLK => (Q[15] : D[15])) = (t_rise, t_fall);
    endspecify

endmodule
`endcelldefine
