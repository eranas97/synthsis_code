
module localvars;
    reg clk;
    reg a;
    reg b;
    reg c;
    reg d;
    int data;
    int data_out;

typedef struct {int ia; logic lb;} tuv;

    initial begin
        clk <= 0;
        a <= 0;
        b <= 0;
        c <= 1;
        d <= 0;
        data = 1;
        data_out = 0;
    end

    always #100 clk <= ~clk;

    initial #5000 $finish;

	simple: assert property(@(posedge clk) \sno+rep_v );
	rep: assert property(@(posedge clk)rep_v);
	assert property(@(posedge clk)rep_v);
    sequence \sno+rep_v ;
        int myint;
		logic mybit;
		logic [7:0]mybus;
        int myotherint;
		tuv lv;
        (a, lv.ia = 2001, lv.lb=1'b0, myint = 0, myotherint = 1, mybit = 1'bx, mybus = 8'bz) ##0
        (!b, myint = myint+data+2, mybus = 8'h5a) ##1
        (!c, lv.ia = 2012, lv.lb=1'b1, myotherint = myotherint*2, mybit = 1'b1) ##1
		(data_out == myint, mybit = 1'b1, mybus = 8'b1);
    endsequence

    sequence rep_v;
        int myint;
        ((a == b),myint = 0) ##0
        (!a [* 0:1] ##1 c, myint = myint+data)[*2] ##1 d ##1 c && (data_out == myint);
    endsequence
endmodule

