module hello_top;

import "DPI-SC" context task sc_task();
export "DPI-SC" task verilog_task;

task verilog_task();
  #10
  $display("#%d hello from verilog_task.", $time);
  #20
  $display("#%d hello from verilog_task.", $time);
endtask

initial
begin

  $display("#%d starting test.", $time);

  sc_task();

  #2000 $finish;
end 
endmodule
