/*********************************************************/
// MODULE:    DRAM Controller
//
// FILE NAME: dramcon_rtl.v
//
/*********************************************************/

// DEFINES
`define DEL	1		// Clock-to-output delay. Zero
					// time delays can be confusing
					// and sometimes cause problems.
`define RBC_CYC 2	// Number of cycles to assert RAS
					// before asserting CAS
`define CBR_CYC 1	// Number of cycles to assert CAS
					// before asserting RAS
`define RACW_CYC 1	// Number of cycles to assert RAS
					// and CAS together for a write
`define RACR_CYC 2	// Number of cycles to assert RAS
					// and CAS together for a read
`define RACRF_CYC 1	// Number of cycles to assert RAS
					// and CAS together for a refresh
`define CNT_BITS 2	// Number of bits needed for the
					// counter to count the cycles
					// listed above
`define REF_CNT 24	// Number of cycles between refreshes
`define REF_BITS 5	// Number of bits needed for the
					// counter to count the cycles
					// for a refresh
`define AOUT 4 		// Address bit width to DRAM
`define AIN 2*`AOUT	// Address bit width from processor

// TOP MODULE
module dram_control(
		clk,
		reset_n,
		as_n,
		addr_in,
		addr_out,
		rw,
		we_n,
		ras_n,
		cas_n,
		ack);

  // INPUTS
  input            clk;      // State machine clk
  input            reset_n;    // Active low, synchronous reset
  input            as_n;       // Active low address strobe
  input [`AIN-1:0]	addr_in;    // Address from processor
  input	           rw;         // Read/write input
                               // = 1 to read
                               // = 0 to write

  // OUTPUTS
  output [`AOUT-1:0]	addr_out; // Address to DRAM
  output             we_n;     // Write enable output
  output	            ras_n;    // Row Address Strobe to memory
  output             cas_n;    // Column Address Strobe
                               // to memory
  output             ack;      // Acknowledge signal
                               // to processor

  // SIGNAL DECLARATIONS
  wire               clk;
  wire               reset_n;
  wire [`AIN-1:0]    addr_in;
  wire               as_n;
  wire               rw;
  wire               we_n;
  wire               ras_n;
  wire               cas_n;
  wire               ack;
  wire [`AOUT-1:0]   addr_out;

  wire               col_out;   // Output column address
                                // = 1 for column address
                                // = 0 for row address
  reg  [`CNT_BITS-1:0] count;     // Cycle counter
  reg  [`REF_BITS-1:0] ref_count; // Refresh counter
  reg                  refresh;   // Refresh request

  // ENUM STATE ENCODING
  // These bits represent the following signals
  // col_out,ras,cas,ack

  enum reg[3:0] {
	IDLE    = 4'b0000,
	ACCESS  = 4'b0100,
	SWITCH  = 4'b1100,
	RAS_CAS = 4'b1110,
	ACK     = 4'b1111,
	REF1    = 4'b0010,
	REF2    = 4'b0110 } mem_state;

  // ASSIGN STATEMENTS
  // Create the outputs from the states
  assign col_out =  mem_state[3];
  assign ras_n   = ~mem_state[2];
  assign cas_n   = ~mem_state[1];
  assign ack     =  mem_state[0];

  // Deassert we_n high during refresh
`ifdef BUG
  assign #`DEL we_n = rw | (mem_state == REF1);
`else
  assign #`DEL we_n = rw | (mem_state == REF1)
                         | (mem_state == REF2);
`endif

  // Give the row address or column address to the DRAM
  assign #`DEL addr_out = col_out ? addr_in[`AOUT-1:0] :
                          addr_in[`AIN-1:`AOUT];

  // MAIN CODE

  // Look at the rising edge of clk for state transitions
  always @(posedge clk or negedge reset_n) begin
    if (~reset_n) begin
      mem_state <= #`DEL IDLE;
      count <= #`DEL `CNT_BITS'h0;
      ref_count <= #`DEL `REF_CNT;
      refresh <= #`DEL 1'b0;
    end
    else begin
      // Time for a refresh request?
      if (ref_count == 0) begin
        refresh <= #`DEL 1'b1;
        ref_count <= #`DEL `REF_CNT;
      end
      else
        ref_count <= #`DEL ref_count - 1;

      // Decrement cycle counter to zero
      if (count)
        count <= #`DEL count - 1;

      case (mem_state)	// synthesis full_case parallel_case
        IDLE: begin
          // Refresh request has highest priority
          if (refresh) begin
            // Load the counter to assert CAS
            count <= #`DEL `CBR_CYC;
            mem_state <= #`DEL REF1;
          end
          else if (~as_n) begin
            // Load the counter to assert RAS
            count <= #`DEL `RBC_CYC;
            mem_state <= #`DEL ACCESS;
          end
        end
          
        ACCESS: begin
          mem_state <= #`DEL SWITCH;
        end
         
        SWITCH: begin
          if (count == 0) begin
            mem_state <= #`DEL RAS_CAS;
            if (rw)
              count <= #`DEL `RACR_CYC;
            else
              count <= #`DEL `RACW_CYC;
          end
        end
          
        RAS_CAS: begin
          if (count == 0) begin
            mem_state <= #`DEL ACK;
          end
        end
          
        ACK: begin
          mem_state <= #`DEL IDLE;
        end
          
        REF1: begin
          if (count == 0) begin
            mem_state <= #`DEL REF2;
            count <= #`DEL `RACRF_CYC;
          end
        end
          
        REF2: begin
          if (count == 0) begin
            mem_state <= #`DEL IDLE;
            refresh <= #`DEL 1'b0;
          end
        end
      endcase
    end
  end
endmodule		// dram_control
