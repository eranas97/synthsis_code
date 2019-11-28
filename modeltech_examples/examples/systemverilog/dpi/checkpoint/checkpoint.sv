module top;

import "DPI-C" function void register_dpi_callback();

import "DPI-C" function void run();

initial begin
    register_dpi_callback();
    run();
end

endmodule