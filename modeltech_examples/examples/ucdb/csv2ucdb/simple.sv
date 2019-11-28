///////////////////////////////////////////////////////////////////////////////
//
//	Simple testcase for test tracking: covergroups only, random testbench
//	A few other parameters for # clocks and parameterizing covergroups.
//
///////////////////////////////////////////////////////////////////////////////


package p;
	class randomizer_2vec #(int VECSIZE = 3);
		rand bit [0:VECSIZE-1] a;
		rand bit [0:VECSIZE-1] b;

		constraint a_range { ((a>=0) && (a<2**VECSIZE)); }
		constraint b_range { ((b>=0) && (b<2**VECSIZE)); }

		function void get_values(ref bit [0:VECSIZE-1] a_value,
								 ref bit [0:VECSIZE-1] b_value);
			void'(randomize());
			a_value = a;
			b_value = b;
		endfunction

	endclass

endpackage

module top;
	parameter NUMCLOCKS = 25;

	bit clk;
	assign #10 clk = ~clk;

	child1type child1(clk);
	child2type child2(clk);

	int clockcounter = 0;

	always @(posedge clk) begin
		clockcounter++;
		if (clockcounter>NUMCLOCKS)
			$stop;
	end

	initial begin
		$display("NUMCLOCKS = ", NUMCLOCKS);
	end

endmodule


module child1type(input logic clk);
	parameter VECBITS = 3;

	bit [0:VECBITS-1] mybits;
	bit [0:VECBITS-1] clockcounter = 0;
	bit [0:VECBITS-1] ignored;

	p::randomizer_2vec #(VECBITS) randomizer = new;

	covergroup cvg_bits_vs_clock @(negedge clk);
		type_option.weight = 2;
		coverpoint mybits;
		coverpoint clockcounter;
		mybits_x_clockcounter: cross mybits, clockcounter;
	endgroup

	cvg_bits_vs_clock cv1  = new;

	always @(posedge clk)
	begin
		clockcounter++;
		randomizer.get_values(mybits,ignored);
		cv1.sample();
	end

	bit [0:VECBITS-1] mybits1;
	bit [0:VECBITS-1] mybits2;

	covergroup cvg_bits_vs_bits @(negedge clk);
		coverpoint mybits1 { type_option.weight = 0; }
		coverpoint mybits2 { type_option.weight = 0; }
		mybits1_x_mybits2: cross mybits1, mybits2;
	endgroup

	cvg_bits_vs_bits cv2 = new;

	always @(posedge clk)
	begin
		clockcounter++;
		randomizer.get_values(mybits1,mybits2);
		cv2.sample();
	end

endmodule


module child2type(input logic clk);
	parameter VECBITS = 3;

	bit [0:VECBITS-1] val1;
	bit [0:VECBITS-1] val2;
	bit [0:VECBITS-1] val3;
	bit [0:VECBITS-1] val4;

	covergroup cvg_arith(ref bit [0:VECBITS-1] value1, value2, input string myname);
		option.name = myname;
		option.per_instance = 1;
		sum: coverpoint int'(value1)+int'(value2) {
			type_option.weight = 0;
			bins sum[] = { [0:2*(2**VECBITS-1)] };
		}
		diff: coverpoint int'(value1)-int'(value2) {
			type_option.weight = 0;
			bins sum[] = { [-(2**VECBITS)+1:2**VECBITS-1] };
		}
		sum_x_diff: cross sum, diff {
			option.weight = 8;
		}
	endgroup

	p::randomizer_2vec #(VECBITS) randomizer = new;
	cvg_arith cv12 = new(val1,val2,"val1_val2");
	cvg_arith cv34 = new(val3,val4,"val3_val4");

	always @(posedge clk) 
	begin
		randomizer.get_values(val1,val2);
		randomizer.get_values(val3,val4);
		cv12.sample();
		cv34.sample();
	end

endmodule
