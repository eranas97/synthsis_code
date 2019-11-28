//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

`timescale 1 ns / 1 ns

module cache(clk, paddr, pdata, prw, pstrb, prdy,
                  saddr, sdata, srw, sstrb, srdy);
    input  clk, srdy, paddr, prw, pstrb;
    output      prdy, saddr, srw, sstrb;
    inout  sdata, pdata;

    `define addr_size  8
    `define set_size   5
    `define word_size  16

    reg verbose;

    reg [`word_size-1:0] sdata_r, pdata_r;
    reg [`addr_size-1:0] saddr_r;
    reg                  srw_r, sstrb_r, prdy_r;

    wire [`addr_size-1:0]      paddr;
    wire [`addr_size-1:0] #(5) saddr = saddr_r;
    wire [`word_size-1:0] #(5) sdata = sdata_r, pdata = pdata_r;
    wire                  #(5) srw   = srw_r, sstrb = sstrb_r, prdy = prdy_r;

    reg  [3:0] oen, wen;
    wire [3:0] hit;

    /**************** Cache sets ****************/
    cache_set s0(paddr, pdata, hit[0], oen[0], wen[0]);
    cache_set s1(paddr, pdata, hit[1], oen[1], wen[1]);
    cache_set s2(paddr, pdata, hit[2], oen[2], wen[2]);
    cache_set s3(paddr, pdata, hit[3], oen[3], wen[3]);

    initial begin
        verbose = 1;
        saddr_r = 0;
        sdata_r = 'bz;
        pdata_r = 'bz;
        srw_r = 0;
        sstrb_r = 1;
        prdy_r = 1;
        oen = 4'b1111;
        wen = 4'b1111;
    end

    /**************** Local MRU memory ****************/

    reg [2:0] mru_mem [0:(1 << `set_size) - 1];

    integer i;
    initial for (i = 0; i < (1 << `set_size); i=i+1) mru_mem[i] = 0;

    function integer hash;
        input [`addr_size-1:0] a;
        hash = a[`set_size - 1:0];
    endfunction

    task update_mru;
        input [`addr_size-1:0] addr;
        input [3:0] hit;
        reg [2:0] mru;
        begin
            mru = mru_mem[hash(addr)];
            mru[2] = ((hit & 4'b1100) != 0);
            if (mru[2]) mru[1] = hit[3];
            else        mru[0] = hit[1];
            mru_mem[hash(addr)] = mru;
        end
    endtask

    function [3:0] pick_set;
        input [`addr_size-1:0] addr;
        integer setnum;
        begin
            casez (mru_mem[hash(addr)])
                3'b1?1 : setnum = 0;
                3'b1?0 : setnum = 1;
                3'b01? : setnum = 2;
                3'b00? : setnum = 3;
                default: setnum = 0;
            endcase
            if (verbose) begin
                if (prw == 1)
                    $display("%t: Read miss, picking set %0d", $time, setnum);
                else
                    $display("%t: Write miss, picking set %0d", $time, setnum);
            end
            pick_set = 4'b0001 << setnum;
        end
    endfunction

    /**************** System Bus interface ****************/
    task sysread;
        input  [`addr_size-1:0] a;
        begin
            saddr_r = a;
            srw_r = 1;
            sstrb_r = 0;
            @(posedge clk) sstrb_r = 1;
            assign prdy_r = srdy;
            assign pdata_r = sdata;
            @(posedge clk) while (srdy != 0) @(posedge clk) ;
            deassign prdy_r;  prdy_r = 1;
            deassign pdata_r; pdata_r = 'bz;
        end
    endtask

    task syswrite;
        input  [`addr_size-1:0] a;
        begin
            saddr_r = a;
            srw_r = 0;
            sstrb_r = 0;
            @(posedge clk) sstrb_r = 1;
            assign prdy_r = srdy;
            assign sdata_r = pdata;
            @(posedge clk) while (srdy != 0) @(posedge clk) ;
            deassign prdy_r;  prdy_r = 1;
            deassign sdata_r; sdata_r = 'bz;
            sdata_r = 'bz;
        end
    endtask

    /**************** Cache control ****************/

    function [3:0] get_hit;
        input [3:0] hit;
        integer setnum;
        begin
            casez (hit)
                4'b???1 : setnum = 0;
                4'b??1? : setnum = 1;
                4'b?1?? : setnum = 2;
                4'b1??? : setnum = 3;
            endcase
            if (verbose) begin
                if (prw == 1)
                    $display("%t: Read hit to set %0d", $time, setnum);
                else
                    $display("%t: Write hit to set %0d", $time, setnum);
            end
            get_hit = 4'b0001 << setnum;
        end
    endfunction

    reg [3:0] setsel;
    always @(posedge clk) if (pstrb == 0) begin
        if ((prw == 1) && hit) begin
            // Read Hit..
            setsel = get_hit(hit);
            oen = ~setsel;
            prdy_r = 0;
            @(posedge clk) prdy_r = 1;
            oen = 4'b1111;
        end else begin
            // Read Miss or Write Hit..
            if (hit)
                setsel = get_hit(hit);
            else
                setsel = pick_set(paddr);
            wen = ~setsel;
            if (prw == 1)
                sysread (paddr);
            else
                syswrite(paddr);
            wen = 4'b1111;
        end
        update_mru(paddr, setsel);
    end
endmodule
