//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Interface Example - Controller
//
`timescale 1ns / 1ns

module CONTROL (MEM_IF.mpCTRL IO, input bit STRT, CLK, output bit STOP);

    typedef enum logic [2:0] {ADD, SUB, NEG, AND, OR, NOT, SHR, SHL} opc_t;

    typedef struct packed {
        opc_t opcode;
        logic [4:0] regA;
        logic [4:0] regB;
        logic [2:0] cnt;
    } instr_t;

    parameter int OFFSET = 16;
    instr_t IR;
    logic [4:0] regC;

    always @(posedge STRT) begin
        for (int address = 0; address <= 10; ++address) begin
            IO.MemRead(address, IR);
            case (IR.opcode)
                ADD:     regC = IR.regA + IR.regB;
                SUB:     regC = IR.regA - IR.regB;
                NEG:     regC = ~IR.regA + 1;
                AND:     regC = IR.regA & IR.regB;
                OR:      regC = IR.regA | IR.regB;
                NOT:     regC = ~IR.regA;
                SHR:     regC = IR.regA >> IR.cnt;
                SHL:     regC = IR.regA << IR.cnt;
                default: regC = 'x;
            endcase
            IO.MemWrite(address + OFFSET, regC);
        end
        STOP = 1;
    end

endmodule
