//
// Simple example that contains nested DPI task and function calls.
//

`timescale 1 ns/1 ns

module top;

int i;
int mcd;

//
// Import decls define name in the current scope, like native tf declarations.
// Prototype parameters are required in ordre to define C function's interface.
//

import "DPI-C" context task CTask(
    input int mcd, level, i1, i2,
    output int o1, o2,
    inout int io1);

import "DPI-C" context function int CFunction(
    input int mcd, level, i1);


//
// Export decls must match a name in the current scope.
// All exported tf's are context by nature.
//
export "DPI-C" task SVTask;
export "DPI-C" function SVFunction;


//
// Exported SV task.  Can be called by either C or SV.
//
task SVTask(
    input int level, i1, i2,
    output int o1, o2,
    inout int io1);
begin
    for (i = 0; i < level; i = i + 1)
        $fwrite(mcd, "   ");
    $fdisplay(mcd, "In SVTask");
    io1 = io1 + 2;
    o1 = CFunction(mcd, level + 1, i1 + 2);
    o2 = CFunction(mcd, level + 1, i2 * 2);
end
endtask

//
// Exported SV function.  Can be called by either C or SV.
//
function int SVFunction(
    input int level, i1);
begin
    for (i = 0; i < level; i = i + 1)
        $fwrite(mcd, "   ");
    $fdisplay(mcd, "In SVFunction");
    SVFunction = i1 * 2;
end
endfunction


int vi1, vi2, vo3, vo4, vb5; 

initial begin
    
    mcd = $fopen("results.txt") | 1;
    vi1 = 'h2;
    vi2 = 'h3;
    vb5 = 'h4;
    CTask(mcd, 1, vi1, vi2, vo3, vo4, vb5);
    $fdisplay(mcd, "%4d: vi1=%4x vi2=%4x vo3=%4x vo4=%4x vb5=%4x",
        $time, vi1, vi2, vo3, vo4, vb5); 
    #5;

    vi1 = vo3;
    vi2 = vo4;
    CTask(mcd, 1, vi1, vi2, vo3, vo4, vb5);
    $fdisplay(mcd, "%4d: vi1=%4x vi2=%4x vo3=%4x vo4=%4x vb5=%4x",
        $time, vi1, vi2, vo3, vo4, vb5); 
    #5;

    vi1 = vo3;
    vi2 = vo4;
    CTask(mcd, 1, vi1, vi2, vo3, vo4, vb5);
    $fdisplay(mcd, "%4d: vi1=%4x vi2=%4x vo3=%4x vo4=%4x vb5=%4x",
        $time, vi1, vi2, vo3, vo4, vb5); 
    #5;

    vi1 = vo3;
    vi2 = vo4;
    CTask(mcd, 1, vi1, vi2, vo3, vo4, vb5);
    $fdisplay(mcd, "%4d: vi1=%4x vi2=%4x vo3=%4x vo4=%4x vb5=%4x",
        $time, vi1, vi2, vo3, vo4, vb5); 
    #5;
    $fclose(mcd);
end

endmodule
