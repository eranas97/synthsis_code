//
//	This shows a covergroup in a package, with per-instance coverage and a
//	cross.
//
package coverpkg;
	covergroup statecover(ref bit i, bit [1:0] state);
		type_option.strobe = 1;
		option.per_instance = 1;
		cvpi: coverpoint i;
		cvpstate: coverpoint state;
		i_x_state: cross cvpi, cvpstate;
	endgroup
endpackage

//
//	Simple general testcase with all kinds of coverage
//
module statemach(input bit i,
			     input bit reset,
                 input bit clk,
                 output bit[1:0] state_out);
    enum { st0, st1, st2, st3 } state;

	coverpkg::statecover iocov = new(i,state_out);

    always @(posedge clk or posedge reset)
    begin
		iocov.sample();
        if (reset)
            state = st0;
        else 
            case(state)
                st0: if (i==0) state = st2;
                     else      state = st1;
                st1: if (i==0) state = st1;
                     else      state = st2;
                st2: if (i==0) state = st1;
                     else      state = st2;
                st3: if (i==0) state = st1;
                     else      state = st3;
            endcase
    end

    always @(state)
        state_out = state;

    covergroup machcover @(state);
    st: coverpoint state;
    reset: coverpoint state {
        bins resetseq[] = ( st1,st2 => st1,st2 => st0 );
    }
    endgroup

    machcover cov;

    initial cov = new;

endmodule

module fibonacci(input bit reset,
                 input bit clk,
                 output integer fib_val);

    bit follow_on_phase;
    integer fib_num = 0;
    integer fib_m1 = 0;
    integer fib_new = 0;

    always @(posedge clk or posedge reset)
    begin      
        // This is written this way to cause expression coverage -- DO NOT REWRITE OPTIMALLY
        follow_on_phase = (!(reset | ((fib_m1 == 0) & (fib_num == 0))));   
        // This is written this way to cause condition  coverage -- DO NOT REWRITE OPTIMALLY
        if (reset || ((fib_m1 == 0) && (fib_num == 0))) begin 
            fib_m1 = 1;
            fib_num = (!(reset == 1));
        end
        if (follow_on_phase) begin    // This is an ELSE
            fib_new = (fib_m1 + fib_num);
            fib_m1 = fib_num;
            fib_num = fib_new;
        end
        fib_val = fib_num;
    end

endmodule

module verilog_toggle(input bit clk);
    typedef enum {one, two, three, four} enumt;
    integer state = 1;
    enumt enums = one;
    reg regs = 1'b0;
    reg [1:0]regv = 2'b01;
    wire wirs = 0;
    wire [1:0]wirv = 2'b01;

    assign wirs = regs;
    assign wirv = regv;

    always @(posedge clk)
    begin
        case (state)
        1:
              begin
                  state = 2;
                  enums = two;
                  regs = 1'b1;
                  regv = 2'b10;
              end
        2:
              begin
                  state = 3;
                  enums = three;
                  regs = 1'bx;
                  regv = 2'bxx;
              end
        default:
              begin
                  state = 1;
                  enums = one;
                  regs = 1'b0;
                  regv = 2'b01;
              end
        endcase;
    end
endmodule

module top;
    bit [1:0] st;
    bit [1:0] st2;
    bit i;
    bit reset = 0;
    bit clk = 0;
    integer fib_val;
    bit primary_yellow;
    bit primary_red;
    bit primary_blue;

    always #50 clk = ~clk;

    always @(st)
        $display("st = %d\n", st);
    always @(st2)
        $display("st2 = %d\n", st2);

	statemach mach(i,reset,clk,st);
	statemach machinv(~i,reset,clk,st2);

	fibonacci fib(reset,clk,fib_val);
    vhdl_color colors(clk, primary_yellow, primary_red, primary_blue);
    verilog_toggle vlog_toggle(clk);
    vhdl_toggle toggle(clk);

    initial begin;
        @(negedge clk); 
            i = 0; reset = 0;
            primary_yellow = 0; primary_red = 0; primary_blue = 0;
        @(negedge clk); 
            i = 0; reset = 0;
            primary_yellow = 1; primary_red = 1; primary_blue = 0;
        @(negedge clk); 
            i = 0; reset = 1;
            primary_yellow = 0; primary_red = 0; primary_blue = 0;
        @(negedge clk); 
            i = 1; reset = 0;
            primary_yellow = 0; primary_red = 1; primary_blue = 1;
        @(negedge clk); 
            i = 1; reset = 0;
            primary_yellow = 0; primary_red = 0; primary_blue = 0;
        @(negedge clk); 
            i = 1; reset = 1;
            primary_yellow = 1; primary_red = 0; primary_blue = 1;
        @(negedge clk); 
            i = 0; reset = 0;
            primary_yellow = 0; primary_red = 0; primary_blue = 0;
        @(negedge clk);
            primary_yellow = 1; primary_red = 1; primary_blue = 1;
        @(negedge clk);
            primary_yellow = 0; primary_red = 0; primary_blue = 0;
        @(negedge clk);
            primary_yellow = 1; primary_red = 0; primary_blue = 0;
        @(negedge clk);
            primary_yellow = 0; primary_red = 1; primary_blue = 0;
        @(negedge clk);
            primary_yellow = 0; primary_red = 0; primary_blue = 1;
        @(negedge clk); $stop;
    end

// psl default clock = rose(clk);
// psl assert_i_after_reset: assert always ({reset} |-> {i}) report "i did not follow reset";
// psl cover_i_after_reset: cover {reset;i} report "i did follow reset" ;

    sequence seq;
        reset;
    endsequence

    property prop;
        @(posedge clk) seq;
    endproperty

    assert_prop:assert property (prop)
        $display("\n reset asserted\n");
    else 
        $display("\n reset de-asserted\n");

endmodule


