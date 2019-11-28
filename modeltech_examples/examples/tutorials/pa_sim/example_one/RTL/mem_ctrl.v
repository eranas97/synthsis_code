`timescale 1ns/1ns

module mem_ctrl (
    input clk, rstn, do_rdy,
    input [1:0] memsel,
    //input  mc_pwr, mc_save, mc_restore,
    //output mc_pwr_ack,
    output reg do_acpt,
    output reg [3:0] ceb, web,
    output reg [7:0] addr);

    // state encoding & FSM variables
    parameter S0  = 4'd0;
    parameter S1  = 4'd1;
    parameter S2  = 4'd2;
    parameter S3  = 4'd3;
    parameter S4  = 4'd4;
    parameter S5  = 4'd5;
    parameter S6  = 4'd6;
    parameter S7  = 4'd7;
    parameter S8  = 4'd8;
    parameter S9  = 4'd9;
    parameter S10 = 4'd10;
    reg [3:0] present_state, next_state;
    
    // model pwr_ack -- changed post DC synthesis
    //buf( mc_pwr_ack, mc_pwr);

    // FSM state register
    always @(posedge clk or negedge rstn)
        if (rstn == 1'b0) begin
            present_state <= S0;
            addr <= 0;
        end
        else begin
            present_state <= next_state;
            addr <= (present_state == S1) ? (addr + 1'b1) : addr ;  // address pointer
        end 

    // FSM next state & output logic
    always @(*) begin
        do_acpt = 1'b0;
        {ceb, web} = 8'b11111111;
        case (present_state) // synopsys full_case
            S0: if (do_rdy)
                    next_state = S1;
                else
                    next_state = S0;
            S1: begin
                    next_state = S2;
                end
            S2: begin
                    case (memsel)
                        2'b00 : {ceb, web} = 8'b11101110;
                        2'b01 : {ceb, web} = 8'b11011101;
                        2'b10 : {ceb, web} = 8'b10111011;
                        2'b11 : {ceb, web} = 8'b01110111;
                    endcase
                    next_state = S3;
                end
            S3: begin
                    {ceb, web} = 8'b11111111;
                    do_acpt = 1'b1;
                    next_state = S4;
                end
            S4: begin
                    do_acpt = 1'b1;
                    next_state = S5;
                end
            S5: next_state = S6;
            S6: begin
                    case (memsel)
                        2'b00 : ceb = 4'b1110;
                        2'b01 : ceb = 4'b1101;
                        2'b10 : ceb = 4'b1011;
                        2'b11 : ceb = 4'b0111;
                    endcase
                    next_state = S7;
                end
            S7: next_state = S8;
            S8: next_state = S9;
            S9: begin
                    ceb = 4'b1111;
                    next_state = S10;
                end
            S10: next_state = S0;
            default: next_state = S0;
        endcase
    end

endmodule
