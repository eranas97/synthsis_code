interface KBus (input clk);
    logic [7:0] addr;
    logic [7:0] data;
    logic stb;
    logic wr;
    logic uga;
    logic rdy_l;
    logic err_l;

    default clocking dfck @(posedge clk); endclocking

    clocking msck @(posedge clk);
        input #1step rdy_l, err_l;
    endclocking

    task sl_drive_data(logic [7:0] d);
        data = d;
    endtask

    task ms_drive_data(logic [7:0] d);
        data = d;
    endtask

    function logic [7:0] sl_get_data();
        return data;
    endfunction

    function logic [7:0] ms_get_data();
        return data;
    endfunction

    task set_rdy(logic v);
        rdy_l = v;
    endtask

    task set_err(logic v);
        err_l = v;
    endtask
    

    task rdy_err_seen;
        while(msck.rdy_l !== 0 && msck.err_l !== 0) begin
            ##1;
        end
        // $display("%t rdy or err", $time);
    endtask
            
    task cycle_wait(int n);
        ##(n);
    endtask

    task ms_write(logic [7:0] a, logic [7:0] d);
        stb = 1;
        wr = 1;
        addr = a;
        data = d;
        rdy_err_seen;
        stb = 0;
    endtask

    task ms_read(logic [7:0] a, output [7:0] d);
        stb = 1;
        wr = 0;
        addr = a;
        rdy_err_seen;
        d = data;
        stb = 0;
    endtask

endinterface

module ram #(parameter int id = 0) (KBus ibus, input cs);
    logic [7:0] mem[0:255];

    initial begin
        ibus.set_rdy(1'bz);
        ibus.set_err(1'bz);
    end

    always @(posedge ibus.dfck)
        if (cs) 
            if (ibus.stb) begin
                if (ibus.addr > 200) begin // error condition
                    ibus.set_err(0);
                    ibus.cycle_wait(1);
                    ibus.set_err(1'bz);
                end
                else begin
                    if (ibus.wr) begin
                        ibus.cycle_wait(1);
                        mem[ibus.addr] = ibus.sl_get_data();
                        $display("%t ram(%0d) written data = %x",
                            $time, id, mem[ibus.addr]);
                    end
                    else
                        ibus.sl_drive_data(mem[ibus.addr]);
                    ibus.set_rdy(0);
                    ibus.cycle_wait(1);
                    ibus.set_rdy(1'bz);
                end
            end
endmodule

program tb(KBus ibus, output logic [1:0] cs);
    class Stim;
        rand bit [7:0] a;
        rand bit [7:0] d;
        rand bit [1:0] cs;
        constraint c1 {
            a dist {[0:200] := 10, [201:255] := 1};
            cs inside {1, 2};
        }
    endclass

    int i;
    logic [7:0] read_d;

    Stim st = new;

    initial begin
        // cs = 0;
        ibus.cycle_wait(2);
        for (i = 0; i < 5; i++) begin
            if (!st.randomize())
                $display("ransomize failed");
            cs = st.cs;
            ibus.ms_write(st.a, st.d);
            ibus.cycle_wait(1);
            ibus.ms_read(st.a, read_d);
            $display("%t read data = %x", $time, read_d);
            assert (read_d == st.d);            
            ibus.cycle_wait(1);
        end
        $display("test completed!!");
        $stop();
    end

endprogram

module top;
    logic [1:0] cs;
    logic clk;
    KBus ibus(clk);

    ram #(0) dut0 (ibus, cs[0]);
    ram #(1) dut1 (ibus, cs[1]);
    tb  tb1(ibus, cs);

    initial begin
      clk = 0;
      forever #5ns clk = ~clk;
    end

    covergroup cg @(posedge ibus.clk);
		option.auto_bin_max = 256;
        Wrb: coverpoint ibus.wr iff (ibus.stb) {
            bins write = { 1 };
            bins read = { 0 };
        }
        Addr: coverpoint ibus.addr iff (ibus.stb) {
            bins a_normal = { [0:200] };
            bins a_err    = { [201:255] };
        }
        Data: coverpoint ibus.data iff(ibus.stb);
        Csb: coverpoint cs iff (ibus.stb) {
            bins r0 = { 2'b01 };
            bins r1 = { 2'b10 };
            illegal_bins noram = {0, 3};
//            illegal_bins noram = {0, 3, 2'bxx };
        }
    endgroup

    cg cg_1 = new;
endmodule
