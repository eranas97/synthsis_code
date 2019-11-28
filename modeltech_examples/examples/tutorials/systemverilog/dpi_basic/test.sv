module test ();

typedef enum {RED, GREEN, YELLOW} traffic_signal;

traffic_signal light;

function void sv_GreenLight ();
begin
	light = GREEN;
end
endfunction

function void sv_YellowLight ();
begin
	light = YELLOW;
end
endfunction

function void sv_RedLight ();
begin
	light = RED;
end
endfunction

task sv_WaitForRed ();
begin
	#10;
end
endtask

export "DPI-C" function sv_YellowLight;
export "DPI-C" function sv_RedLight;
export "DPI-C" task sv_WaitForRed;

import "DPI-C" context task c_CarWaiting ();

initial
begin
	#10 sv_GreenLight;
	#10 c_CarWaiting;
	#10 sv_GreenLight;
end

endmodule
