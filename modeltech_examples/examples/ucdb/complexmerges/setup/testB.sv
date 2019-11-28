module bench;
	bit clk = 0;
	bit a, b;
	first F1(clk);
	first #(10) THIS_NAME_DOES_NOT_MATCH(clk);

	always #50 clk = ~clk;

endmodule

module first(input clk);

	int first_int = 0;
	parameter P = 5;

	always @(negedge clk) first_int++;

	covergroup mycvg_in_first (int numbins) @(negedge clk);
		//option.per_instance = 1;
        coverpoint first_int {
            bins multi_val[5] = { [ 0:numbins-1 ] };
        }
    endgroup

	mycvg_in_first myVar1_first = new(10);

	initial begin: begin1
		//mycvg_in_first myVar1_beg1;
		//myVar1_beg1 = new(5);
		fork : fork1
			first_int = 2;
			first_int = 3;
		join;
	end

	second S1(clk);
endmodule

module second(input clk);
	int int1, int2;
	reg b0, b1, b2, b3;

	// psl default clock = rose(clk);
    // psl psl_cover: cover { int1==int2 } @(negedge clk);

    // psl psl_assert: assert { int1==int2 } @(negedge clk);

    // psl endpoint psl_s_e = {b1[*2]; [*0:2]; b2};
    // psl property psl_p0 = always {b0} |=> {{psl_s_e; b3[*5]} : {psl_s_e}};
    // psl assert psl_p0;

    sequence int1_eq_int2;
        @(negedge clk) ( int1==int2 );
    endsequence

    sva_cover: cover property(int1_eq_int2);
    sva_cover1: cover property(int1_eq_int2);
    cover property(int1_eq_int2);
    sva_assert: assert property(int1_eq_int2);


    sequence s0;
     @(posedge clk) b1[*2] ##[1:3] ##1 b2;
    endsequence

    property p1;
     @(posedge clk) b0 |-> s0.ended;
    endproperty

    //assert property (@(posedge clk) p1);
    assert property (@(posedge !clk) p1);

	class myclass;
		covergroup mycvgt (int numbins) @(negedge clk);
			option.per_instance = 1;
			coverpoint int1 {
				bins multi_val[5] = { [ 0:numbins-1 ] };
			}
		endgroup
        function new(int val);
            int1 = val;
            int2 = val;
			mycvgt = new(val);
        endfunction
    endclass

	myclass cl1 = new(10);
	interf intf();

	task tsk;
		input i;
		output o;
		o = i;
	endtask

	function ffn;
		input i;
		ffn = i;
	endfunction
endmodule

interface interf;

    int int1 = 0;
    int int2 = 0;
    logic clk = 0;

    //  This tests instance coverage in a very simple case.
    //
    covergroup covertype (int cross_at_least) @(negedge clk);

        //option.per_instance = 1;

        coverpoint int1 {
            option.at_least = 2;
            bins mybins[] = { 0, 1 };
        }
        coverpoint int2 {
            option.at_least = 4;
            option.weight = 2;
            type_option.weight = 3;
            bins mybins[] = { 0, 1 };
        }

        int1_x_int2: cross int1, int2 {
            option.weight = 2;
            type_option.weight = 4;
            option.at_least = cross_at_least;
        }

    endgroup
	covertype intf_cvg = new(2);

endinterface: interf
