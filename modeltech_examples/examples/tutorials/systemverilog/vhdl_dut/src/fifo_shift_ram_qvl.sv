module fifo_shift_ram_props (
  input clk, reset_n, ram_re, ram_we,
  input [10:0] push, addra, addrb, 
  waddr1, waddr2, waddr3, waddr4,
  waddr5, waddr6, waddr7, waddr8,
  waddr9, waddr10, waddr11,
  raddr1, raddr2, raddr3, raddr4,
  raddr5, raddr6, raddr7, raddr8,
  raddr9, raddr10, raddr11,
  input [3:0] sel
  );

reg [10:0] fifo_select;

// Verify that only one level of the RAM is written at a time
qvl_mutex #(
        .severity_level(`QVL_ERROR),
        .property_type(`QVL_ASSERT),
        .msg("QVL_VIOLATION : "),
        .coverage_level(`QVL_COVER_NONE),
        .width(11))
        qvl_mutex_instance(
                .clk(clk),
                .reset_n(reset_n),
                .active(ram_we),
                .test_expr(push)
        );

// fifo_shift_ram does not function like a traditional fifo
/*
     qvl_fifo #(
        .severity_level(`QVL_ERROR),
        .property_type(`QVL_ASSERT),
        .msg("QVL_VIOLATION : "),
        .coverage_level(`QVL_COVER_NONE),
        .depth(17),
        .width(8),
        .pass(0),
        .registered(0),
        .high_water(0),
        .full_check(0),
        .empty_check(0),
        .value_check(0),
        .latency(0),
        .preload_count(0))
      qvl_fifo_instance(
        .clk(clk),
        .reset_n(reset_n),
        .active(1'b0),
        .enq(push[0]),
        .deq(ram_re&&push[0]),
        .full(),
        .empty(),
        .enq_data(),
        .deq_data(),
        .preload()
        );
*/

qvl_memory_access #(
        .severity_level(`QVL_ERROR),
        .property_type(`QVL_ASSERT),
        .msg("QVL_VIOLATION : "),
        .coverage_level(`QVL_COVER_NONE),
        .addr_width(11),
        .read_old_data(0),
        .initialized_check(0),
        .single_access_check(1),
        .single_write_check(1),
        .single_read_check(0),
        .data_check(0),
        .data_width(8),
        .latency(0))
        qvl_memory_access_instance(
                .clk(clk),
                .reset_n(reset_n),
                .active(1'b1),
                .read_addr(addrb),
                .read_data(),
                .read(ram_re),
                .write_addr(addra),
                .write_data(),
                .write(ram_we),
                .start_addr(11'b0),
                .end_addr(11'h7FF)
        );

parameter integer g_min[0:10] = '{0, 64, 128, 256, 384, 512, 640, 768, 1024, 1280, 1536};
parameter integer g_max[0:10] = '{16, 97, 178, 323, 468, 613, 758, 903, 1176, 1449, 1722};

// fifo select mux
/*
always @(sel) 
case (sel) 
	4'b0000:	fifo_select = 11'b00000000001;
	4'b0001:	fifo_select = 11'b00000000010;
	4'b0010:	fifo_select = 11'b00000000100;
	4'b0011:	fifo_select = 11'b00000001000;
	4'b0100:	fifo_select = 11'b00000010000;
	4'b0101:	fifo_select = 11'b00000100000;
	4'b0110:	fifo_select = 11'b00001000000;
	4'b0111:	fifo_select = 11'b00010000000;
	4'b1000:	fifo_select = 11'b00100000000;
	4'b1001:	fifo_select = 11'b01000000000;
	4'b1010:	fifo_select = 11'b10000000000;
	default:	fifo_select = 11'b00000000000;
endcase
*/
assign fifo_select = (sel < 4'd11)? 1<<sel : 11'b0;

generate
   genvar i_gen;
   for (i_gen=0; i_gen < 11; i_gen = i_gen +1) 
     begin

     // Verify that the proper level RAM address is selected
     // and the RAM address is within the acceptable range during a write
     // and post incremented write address is still in acceptable range

     ovl_range #(
	`OVL_ERROR, // severity_level
	11, // width
	g_min[i_gen], // min
	g_max[i_gen], // max
	`OVL_ASSERT, // property_type
	"Error: writing to out-of-range address", // msg
	`OVL_COVER_BASIC, // coverage_level
	`OVL_POSEDGE, // clock_edge
	`OVL_ACTIVE_LOW, // reset_polarity
	`OVL_GATING_TYPE_DEFAULT) // gating_type
     ovl_write_range_check (
	.clock(clk), // clock
	.reset(reset_n), // reset
	.enable(push[i_gen]), // enable
	.test_expr(addra), // test_expr
	.fire()); // fire

     // Verify that the proper level RAM address is selected
     // and the RAM address is within the acceptable range during a read
     ovl_range #(
	`OVL_ERROR, // severity_level
	11, // width
	g_min[i_gen], // min
	g_max[i_gen], // max
	`OVL_ASSERT, // property_type
	"Error: reading from out-of-range address", // msg
	`OVL_COVER_BASIC, // coverage_level
	`OVL_POSEDGE, // clock_edge
	`OVL_ACTIVE_LOW, // reset_polarity
	`OVL_GATING_TYPE_DEFAULT) // gating_type
     ovl_read_range_check (
	.clock(clk), // clock
	.reset(reset_n), // reset
	.enable(ram_re && fifo_select[i_gen]), // enable
	.test_expr(addrb), // test_expr
	.fire()); // fire

     end //for
endgenerate

endmodule
