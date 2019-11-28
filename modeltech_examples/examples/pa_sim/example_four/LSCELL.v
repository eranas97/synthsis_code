`celldefine
(* is_level_shifter = 1 *)
module LSCELL (  I, Z) ;
(* level_shifter_data_pin  = 1 *)input I;
output Z;

assign Z = I;

endmodule
`endcelldefine
