`celldefine
(* is_isolation_cell = 1 *)
module ISOCELL (  I, ISO, Z) ;
(* isolation_cell_data_pin = 1 *)input I;
(* isolation_cell_enable_pin = 1 *)input ISO;
output Z;

assign Z = ISO | I;

endmodule
`endcelldefine
