package interleaver_env_pkg;

   import interleaver_svc_pkg::*;
   import interleaver_tr_pkg::*;
   import avm_pkg::*;


   class interleaver_env #( int PACKET_GEN_NUM = 80, int WIDTH = 8 , int PAYLD_SIZE = 203 )
     extends avm_env;

      typedef pkt_request #( WIDTH , PAYLD_SIZE ) packet_t;
  
      // channels and interface
      local virtual rdyacpt_pins_if #( .WIDTH( WIDTH ) ) int_bus_if;
      local tlm_fifo #( packet_t ) int_channel;
  
      // inteleaver specific components
      local interleaver_nb_driver #( WIDTH , PAYLD_SIZE ) int_driver;
      local interleaver_monitor #( WIDTH , PAYLD_SIZE ) int_monitor;
      local interleaver_stimulus #( WIDTH , PAYLD_SIZE ) int_stimulus;
      local interleaver_score #( PACKET_GEN_NUM, WIDTH , PAYLD_SIZE ) int_score;
      local interleaver_cover #( WIDTH , PAYLD_SIZE ) int_cover;
  
      function new( virtual rdyacpt_pins_if #(.WIDTH(WIDTH)) bus_if );
  
         int_bus_if = bus_if;
         int_channel = new("channel", this);
  
         int_driver   = new("driver", this);
         int_monitor  = new("monitor", this);
         int_stimulus = new("stimulus", this);
         int_score    = new("scoreboard", this);
         int_cover    = new("cover", this);
      endfunction
  
      function void connect();
  
         // connect stimulus and driver to the fifo
         int_stimulus.put_port.connect(int_channel.blocking_put_export);
         int_driver.get_port.connect(int_channel.nonblocking_get_export);
  
         // connect monitor to the bus
         int_monitor.pins_if = int_bus_if;
         int_driver.pins_if = int_bus_if;
         int_monitor.ap.connect(int_score.analysis_export);
         int_monitor.ap.connect(int_cover.analysis_export);

      endfunction

      function void configure();
        set_report_severity_action_hier(ERROR, DISPLAY | LOG );
      endfunction

      task run;

         fork
            int_stimulus.generate_stimulus;
            //int_driver.run;
            terminate;
         join

      endtask

      task terminate;
        begin
          wait(int_score.done | int_score.error); // wait not working so while loop is a kluge
          if(int_score.done) 
            avm_report_message("env tb", "ENV SAW DONE",,`__FILE__,`__LINE__);
          int_stimulus.stop;
          avm_report_message("env tb", "Stimulus generater stoped",,`__FILE__,`__LINE__);
        end
      endtask // terminate

      function void report;
        if (int_score.error)
          pass = 0;
        report_status;
        return;
      endfunction

   endclass

endpackage // interleaver_env
