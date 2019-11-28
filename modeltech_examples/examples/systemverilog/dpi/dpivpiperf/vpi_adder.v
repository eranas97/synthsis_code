module vpi_adder;

parameter L = 40000000;
integer i;
integer accumulate = 0;
integer mcd;

initial begin
    for (i = 1; i <= L; i = i + 1) begin
        accumulate = $add(accumulate, i);
    end
    mcd = $fopen("results.txt") | 1;
    $fdisplay(mcd, "accumulate = %d", accumulate);
    $fclose(mcd);
end

endmodule
