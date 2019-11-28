
import interleaver_env_pkg::interleaver_env;

//----------------------------------------------------------------------
// MODULE top
//----------------------------------------------------------------------
module top;

  rdyacpt_pins_if #( .WIDTH( 8 ) ) pins_if( );
   
  interleaver dut('1,pins_if);  
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
