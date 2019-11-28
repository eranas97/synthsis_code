
import interleaver_env_pkg::interleaver_env;

//----------------------------------------------------------------------
// MODULE top
//----------------------------------------------------------------------
module top;

  rdyacpt_pins_if #( .WIDTH( 8 ) ) pins_if( );
   
  //interleaver_m0 dut(1'b1,pins_if);  
  interleaver_m0 dut(
	.enable(1'b1),
	.clk( pins_if.clk),
	.reset_n(pins_if.reset_n),
	.di_rdy(pins_if.rdy_di),
	.di(pins_if.data_di),
	.di_acpt(pins_if.acpt_di),
	.do_acpt(pins_if.acpt_do),
	.do_rdy(pins_if.rdy_do),
	.do_data(pins_if.data_do)
  );
  clock_reset cr( pins_if );

  interleaver_env #( 80, 8 , 203 )  env;
   
  initial begin
    
    env = new( pins_if );
      
    fork
      cr.run;
    join_none

    env.do_test;
    $finish;
      
  end

endmodule
