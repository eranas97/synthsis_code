/*********************************************************/
// MODULE:		DRAM Controller simulation
//
// FILE NAME:	dramcon_sim.v
// VERSION:		1.0
// DATE:		January 1, 1999
// AUTHOR:		Bob Zeidman, Zeidman Consulting
// 
// CODE TYPE:	Simulation
//
// DESCRIPTION:	This module provides stimuli for simulating
// a DRAM memory controller. It uses a DRAM memory model and
// performs a number of writes and reads, including
// back-to-back reads and writes. It also checks the reset
// function.
//
/*********************************************************/

// DEFINES
`define DEL	1                     // Clock-to-output delay. Zero
                                  // time delays can be confusing
                                  // and sometimes cause problems.
`define DEL2 2                    // Longer clk-to-output delay.
`define ACC_COUNT 4               // Maximum number of cycles needed
                                  // to access memory
`define CLK_HPERIOD 50	           // Clock half period
                                  // Clock period
`define CLK_PERIOD CLK_HPERIOD*2
`define WR_PERIOD 70              // Write access time of memory
                                  // from assertion of CAS
`define RD_PERIOD 120             // Read access time of memory
                                  // from assertion of CAS
`define AOUT 4                    // Address bit width to DRAM
`define AIN 2*`AOUT               // Address bit width from processor
`define DWIDTH 8                  // Data width of DRAM
`define DDEPTH 256                // Data depth of DRAM

// TOP MODULE
module tb();

  // SIGNAL DECLARATIONS
  reg              clk;
  reg              reset;
  reg  [`AIN-1:0]  addr_in;
  reg              as;
  reg              rw;
  wire             we_n;
  wire             ras_n;
  wire             cas_n;
  wire             ack;
  wire [`AOUT-1:0] addr_out;

  reg  [`DWIDTH-1:0]	data_out;	  // Data out of processor
  wire [`DWIDTH-1:0]	data;       // Data bus
  reg  [`AIN:0]      addr_count; // Address counter
  reg  [`DWIDTH-1:0] data_patt;	 // Data pattern holder
  integer            cyc_count;	 // Count cycles to determine
                                 // if the access has taken
                                 // too long


  // ASSIGN STATEMENTS
  assign data = (as & we_n) ? 8'hzz : data_out;

  // MAIN CODE

  // Instantiate the controller
  dram_control cntrl(
		.clk(clk),
		.reset_n(~reset),
		.as_n(~as),
		.addr_in(addr_in),
		.addr_out(addr_out),
		.rw(rw),
		.we_n(we_n),
		.ras_n(ras_n),
		.cas_n(cas_n),
		.ack(ack));

  // Instantiate a DRAM
  dram #(`DWIDTH, `AOUT, `AIN, `DDEPTH, `RD_PERIOD, `WR_PERIOD, `DEL) Dram
             (	.ras(~ras_n),
		.cas(~cas_n),
		.we(~we_n),
		.address(addr_out),
		.data(data)  );

  // Generate the clk
  always #`CLK_HPERIOD clk = ~clk;

  // Simulate
  initial begin
    // Initialize inputs
    clk = 1;
    reset = 0;
    as = 0;

    // Test the reset signal
    #`DEL;
    // Assert the reset signal
    reset = 1;

    // Wait for the outputs to change asynchronously
    #`DEL
    #`DEL

	#`CLK_HPERIOD;
	#`CLK_HPERIOD;
    
    // Test outputs
    if ((ras_n === 1'b1) &&
        (cas_n === 1'b1) &&
        (ack === 1'b0))
    begin
      $display ("Reset is working");
    end
    else begin
      $display("\nERROR at time %0t:", $time);
      $display("Reset is not working");
      $display("    ras_n = %b", ras_n);
      $display("    cas_n = %b", cas_n);
      $display("    ack   = %b\n", ack);
		
      // Use $stop for debugging
      $stop;
    end

    // Deassert the reset signal
    reset = 0;

    // Initialize the address counter
    addr_count = 0;
	
    // Initialize the data pattern to be written
    data_patt = `DWIDTH'h1;

    // Write a series of values to memory
    while (addr_count[`AIN] === 0) begin
      // Write to memory
      writemem(addr_count[`AIN-1:0], data_patt);

      // Increment the address counter
      addr_count <= addr_count + 1;

      // Shift the data pattern
      data_patt <= (data_patt << 1);
      data_patt[0] <= data_patt[`DWIDTH-1];

      // Wait for the data pattern to change
      #`DEL;
    end

    // Initialize the address counter
    addr_count = 0;

    // Initialize the data pattern to be read
    data_patt = `DWIDTH'h1;

    // Verify the values that were written	
    while (addr_count[`AIN] === 0) begin 
      // Read from memory
      readmem(addr_count[`AIN-1:0], data_patt);

      // Increment the address counter
      addr_count <= addr_count + 1;

      // Shift the data pattern
      data_patt <= (data_patt << 1);
      data_patt[0] <= data_patt[`DWIDTH-1];

      // Wait for the data pattern to change
      #`DEL;
    end

    $display("\nSimulation complete - no errors\n");
    $finish;
  end

  // Check the number of cycles for each access
  always @(posedge clk) begin
    // Check whether an access is taking too long
    if (cyc_count > 3*`ACC_COUNT) begin
      $display("\nERROR at time %0t:", $time);
      if (rw)
        $display("Read access took too long\n");
      else
        $display("Write access took too long\n");

      // Use $stop for debugging
      $stop;
    end
  end

  // TASKS
  // Write data to memory
  task writemem;

  // INPUTS
  input [`AIN-1:0]	   write_addr;  // Memory address
  input [`DWIDTH-1:0]	write_data;  // Data to write to memory

  // TASK CODE
  begin
    cyc_count = 0;		// Initialize the cycle count

    // Wait for the rising clk edge
    @(posedge clk);
    rw <= #`DEL 0;                    // Set up a write access
                                      // Set up the address
    addr_in <= #`DEL write_addr;
    
    // Set up the data to be written
    data_out <= #`DEL write_data;
    as <= #`DEL2 1;                  // Assert address strobe

    // Wait for the acknowledge
    @(posedge clk);
    while (~ack) begin
      // Increment the cycle count
      cyc_count = cyc_count + 1;

      @(posedge clk);
    end

    as <= #`DEL 0;       // Deassert address strobe
    @(posedge clk);    // Wait one clk cycle

  end
  endtask               // writemem

  // Read data from memory and check its value
  task readmem;

  // INPUTS
  input [`AIN-1:0]	   read_addr;		// Memory address
  input [`DWIDTH-1:0]	exp_data;   // Expected read data

  // TASK CODE
  begin
    cyc_count = 0;               // Initialize the cycle count

    // Wait for the rising clk edge
    @(posedge clk);
    rw <= #`DEL 1;               // Set up a read access
                                 // Set up the address
    addr_in <= #`DEL read_addr;
    as <= #`DEL2 1;              // Assert address strobe

    // Wait for the acknowledge
    @(posedge clk);
    while (~ack) begin
      // Increment the cycle count
      cyc_count = cyc_count + 1;

      @(posedge clk);
    end

    // Did we find the expected data?
    if (data !== exp_data) begin
      $display("\nERROR at time %0t:", $time);
      $display("Controller is not working");
      $display("    data written = %h", exp_data);
      $display("    data read    = %h\n", data);

      // Use $stop for debugging
      $stop;
    end

    as <= #`DEL 0;      // Deassert address strobe
    @(posedge clk);   // Wait one clk cycle

  end
  endtask       // readmem

endmodule       // dramcon_tb
