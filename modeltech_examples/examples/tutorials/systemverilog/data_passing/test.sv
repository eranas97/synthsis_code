module test ();

import "DPI-C" context function void print_int ( input int int_in );
import "DPI-C" context function void print_logic ( input logic logic_in );

int int_var;
bit bit_var;
logic logic_var;

initial
begin
	print_int(int_var);
	int_var = 1;
	print_int(int_var);
	int_var = -12;
	print_int(int_var);
        print_int(bit_var);
        bit_var = 1'b1;
        print_int(bit_var);
	bit_var = 1'bx;
	print_int(bit_var);
	logic_var = 1'b1;
	print_int(logic_var);
	logic_var = 1'bx;
	print_int(logic_var);
        print_logic(logic_var);
	logic_var = 1'bz;
	print_logic(logic_var);
	logic_var = 1'b0;
	print_logic(logic_var);
end

endmodule
