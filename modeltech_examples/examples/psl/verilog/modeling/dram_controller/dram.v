// SUBMODULE
// DRAM memory model
module dram(
             ras,
             cas,
             we,
             address,
             data);

  // PARAMETERS
  parameter DWIDTH = 8;
  parameter AOUT = 4;
  parameter AIN = 2*AOUT;
  parameter DDEPTH = 256;
  parameter RD_PERIOD = 120;
  parameter WR_PERIOD = 70;
  parameter DEL = 1;

  // INPUTS
  input ras;                // Row address strobe
  input cas;                // Column address strobe
  input we;                 // Write enable input
  input [AOUT-1:0]	address;	// Address input to DRAM

  // INOUTS
  inout [DWIDTH-1:0]	data;	 // Data lines

  // SIGNAL DECLARATIONS
  wire ras;
  wire cas;
  wire we;
  wire [DWIDTH-1:0]	data;
  reg  [DWIDTH-1:0]	mem[DDEPTH-1:0]; // Stored data
  reg  [AIN-1:0]    mem_addr;			     // Memory address

  time rd_time;		                    // Time of the most recent change of
                                     // the rd input
  wire [63:0]	rd_dtime;              // rd_time delayed by RD_PERIOD
                                     // time units

  time wr_time;                      // Time of the most recent change of
                                     // the wr input
  wire [63:0]	wr_dtime;              // wr_time delayed by WD_PERIOD
                                     // time units

  reg  oen;                          // Internal output enable - this
                                     // signal is asserted after the
                                     // minimum CAS time for a read
  reg  wen;                          // Internal write enable - this
                                     // signal is asserted after the
                                     // minimum CAS time for a write

  // ASSIGN STATEMENTS
  assign #RD_PERIOD rd_dtime = rd_time;
  assign #WR_PERIOD wr_dtime = wr_time;

  // Output the data if the we signal is high and the oe is
  // asserted, which means that we met the minimum CAS time
  // for a read
  assign data = (oen & ~we) ? mem[address] : 8'hzz;

  // MAIN CODE
  initial begin
    oen = 0;
    wen = 0;
    wr_time = 0;
    rd_time = 0;
  end

  // Look for the RAS rising edge for the row address
  always @(posedge ras) begin
    mem_addr[AIN-1:AOUT] <= #DEL address;
  end 

  // Look for the CAS rising edge for the column address
  always @(posedge cas) begin
    mem_addr[AOUT-1:0] <= #DEL address;
  end 

  // Look for the beginning of the access
  always @(posedge cas) begin
    if (we) begin
      // This is a write
      wr_time = $time;    // Save the time of the most
                          // recent rising edge of wr
      wen = 0;            // Deassert internal write enable
    end
    else begin
      // This is a read
      rd_time = $time;    // Save the time of the most
                          // recent rising edge of rd
      oen = 0;            // Deassert internal read enable
    end
  end

  // Determine whether to assert the internal write enable
  always @(wr_dtime) begin
    if (wr_time === wr_dtime) begin
      // If this is true, the last rising edge of CAS
      // was exactly WR_PERIOD time units ago, so
      // assert the internal write enable
      wen = 1;
    end
  end

  // Determine whether to assert the internal read enable
  always @(rd_dtime) begin
    if (rd_time === rd_dtime) begin
      // If this is true, the last rising edge of rd
      // was exactly RD_PERIOD time units ago, so
      // assert the internal output enable
      oen = 1;
    end
  end

  // Look for the end of the access
  always @(negedge cas) begin
    if (wen & we) begin
      // Write the data if the write enable is asserted
      // which means we met the minimum wr pulse time
      mem[mem_addr] <= #DEL data;
    end
    wen = 0;      // Turn off the internal write enable
    oen = 0;      // Turn off the internal output enable
  end

endmodule         // dram
