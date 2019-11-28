module testrand;
  parameter SIM_TIME = 1;
  parameter FSSeed = 50;

int fsLocations;
logic [7:0] FS_STORE [0:65535];

task FillFSStore (
  input Seed, input Zeros
  );
  integer seed ; seed = Seed ;
  for (fsLocations=0;fsLocations<=65535;fsLocations=fsLocations+1)
    begin
      if (Zeros == 0)
        begin
          FS_STORE[fsLocations] <= 8'b00000000;
        end
      else
        begin
          FS_STORE[fsLocations] <= $random(seed);
        end
    end   
endtask

initial // Simulation Run time Control
  begin
    #(SIM_TIME * 1000000);
    $display("Simulation Finished"); 
    $stop();
  end
  
initial // Host generator
  begin
    FillFSStore  (FSSeed,1); 
  end

endmodule