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


// Verify that only one level of the RAM is written at a time
property push_mutex_check;
 @(posedge clk) ram_we |-> ($onehot(push) ##1 !ram_we);
endproperty

assert property (push_mutex_check);

// Verify that the proper level RAM address is selected
// and the RAM address is within the acceptable range during a write
// and post incremented write address is still in acceptable range
property ram_write_check (we, waddr, lorange, hirange);
@(posedge clk) we |-> ((addra == waddr && waddr >= lorange && waddr <= hirange) ##1
                        (!we && waddr >= lorange && waddr <= hirange));
endproperty

assert property (ram_write_check(push[0],  waddr1,  11'd0,    11'd16));
assert property (ram_write_check(push[1],  waddr2,  11'd64,   11'd97));
assert property (ram_write_check(push[2],  waddr3,  11'd128,  11'd178));
assert property (ram_write_check(push[3],  waddr4,  11'd256,  11'd323));
assert property (ram_write_check(push[4],  waddr5,  11'd384,  11'd468));
assert property (ram_write_check(push[5],  waddr6,  11'd512,  11'd613));
assert property (ram_write_check(push[6],  waddr7,  11'd640,  11'd758));
assert property (ram_write_check(push[7],  waddr8,  11'd768,  11'd903));
assert property (ram_write_check(push[8],  waddr9,  11'd1024, 11'd1176));
assert property (ram_write_check(push[9],  waddr10, 11'd1280, 11'd1449));
assert property (ram_write_check(push[10], waddr11, 11'd1536, 11'd1722));

// Verify that the proper level RAM address is selected
// and the RAM address is within the acceptable range during a read
// pl property ram_read_check (boolean rden, radd_eq_ram_add, radd_lowrange, radd_highrange) =
// always {(rden && radd_eq_ram_add)} |-> {radd_lowrange && radd_highrange; !rden};
property ram_read_check (re, raddr, lorange, hirange);
  @(posedge clk) (re && addrb == raddr) |-> ((raddr >= lorange && raddr <= hirange) ##1 !re);
endproperty

assert property (ram_read_check(ram_re, raddr1,  11'd0,    11'd16));
assert property (ram_read_check(ram_re, raddr2,  11'd64,   11'd97));
assert property (ram_read_check(ram_re, raddr3,  11'd128,  11'd178));
assert property (ram_read_check(ram_re, raddr4,  11'd256,  11'd323));
assert property (ram_read_check(ram_re, raddr5,  11'd384,  11'd468));
assert property (ram_read_check(ram_re, raddr6,  11'd512,  11'd613));
assert property (ram_read_check(ram_re, raddr7,  11'd640,  11'd758));
assert property (ram_read_check(ram_re, raddr8,  11'd768,  11'd903));
assert property (ram_read_check(ram_re, raddr9,  11'd1024, 11'd1176));
assert property (ram_read_check(ram_re, raddr10, 11'd1280, 11'd1449));
assert property (ram_read_check(ram_re, raddr11, 11'd1536, 11'd1722));

endmodule
