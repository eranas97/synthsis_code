module fifo_shift_ram #(parameter BUG=0) (
  input clk, reset_n, ram_re,
  input [10:0] push,
  input [7:0] din,
  input [3:0] sel,
  output [7:0] dout
  );

wire [10:0] addra;
wire [10:0] addrb;
reg [10:0] waddr1;
reg [10:0] waddr2;
reg [10:0] waddr3;
reg [10:0] waddr4;
reg [10:0] waddr5;
reg [10:0] waddr6;
reg [10:0] waddr7;
reg [10:0] waddr8;
reg [10:0] waddr9;
reg [10:0] waddr10;
reg [10:0] waddr11;
reg [10:0] raddr1;
reg [10:0] raddr2;
reg [10:0] raddr3;
reg [10:0] raddr4;
reg [10:0] raddr5;
reg [10:0] raddr6;
reg [10:0] raddr7;
reg [10:0] raddr8;
reg [10:0] raddr9;
reg [10:0] raddr10;
reg [10:0] raddr11;
wire ram_we;
/*
function bits1; 
input [10:0] we;
reg [3:0] count;
integer i;
  begin
    count = 4'd0;
    for (i=0; i<11; i=i+1)
      begin
        if (we[i] == 1'b1)
          count = count + 1;
      end
    if (count == 1)
      bits1 = 1'b1;
    else
      bits1 = 1'b0;
  end
endfunction
*/
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

covergroup ram_w1_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {1};
    ignore_bins nowrite = {0,[2:2047]};
  }
  coverpoint waddr1
  { bins valid_addr [] = {[0:16]};
    ignore_bins bad_addr = {[17:2047]};
  }
  waddr1Xpush: cross waddr1, push;
endgroup

covergroup ram_w2_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {2};
    ignore_bins nowrite = {[0:1],[3:2047]};
  }
  coverpoint waddr2
  { bins valid_addr [] = {[64:97]};
    ignore_bins bad_addr = {[0:63], [98:2047]};
  }
  waddr2Xpush: cross waddr2, push;
endgroup

covergroup ram_w3_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {4};
    ignore_bins nowrite = {[0:3],[5:2047]};
  }
  coverpoint waddr3
  { bins valid_addr [] = {[128:178]};
    ignore_bins bad_addr = {[0:127], [179:2047]};
  }
  waddr3Xpush: cross waddr3, push;
endgroup

covergroup ram_w4_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {8};
    ignore_bins nowrite = {[0:7],[9:2047]};
  }
  coverpoint waddr4
  { bins valid_addr [] = {[256:323]};
    ignore_bins bad_addr = {[0:255], [324:2047]};
  }
  waddr4Xpush: cross waddr4, push;
endgroup

covergroup ram_w5_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {16};
    ignore_bins nowrite = {[0:15],[17:2047]};
  }
  coverpoint waddr5
  { bins valid_addr [] = {[384:468]};
    ignore_bins bad_addr = {[0:383], [469:2047]};
  }
  waddr5Xpush: cross waddr5, push;
endgroup

covergroup ram_w6_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {32};
    ignore_bins nowrite = {[0:31],[33:2047]};
  }
  coverpoint waddr6
  { bins valid_addr [] = {[512:613]};
    ignore_bins bad_addr = {[0:511], [614:2047]};
  }
  waddr6Xpush: cross waddr6, push;
endgroup

covergroup ram_w7_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {64};
    ignore_bins nowrite = {[0:63],[65:2047]};
  }
  coverpoint waddr7
  { bins valid_addr [] = {[640:758]};
    ignore_bins bad_addr = {[0:639], [759:2047]};
  }
  waddr7Xpush: cross waddr7, push;
endgroup

covergroup ram_w8_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {128};
    ignore_bins nowrite = {[0:127],[129:2047]};
  }
  coverpoint waddr8
  { bins valid_addr [] = {[768:903]};
    //ignore_ns bad_addr = {[0:767], [904:2047]};
  }
  waddr8Xpush: cross waddr8, push;
endgroup

covergroup ram_w9_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {256};
    ignore_bins nowrite = {[0:255],[257:2047]};
  }
  coverpoint waddr9
  { bins valid_addr [] = {[1024:1176]};
    ignore_bins bad_addr = {[0:1023], [1177:2047]};
  }
  waddr9Xpush: cross waddr9, push;
endgroup

covergroup ram_w10_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {512};
    ignore_bins nowrite = {[0:511],[513:2047]};
  }
  coverpoint waddr10
  { bins valid_addr [] = {[1280:1449]};
    ignore_bins bad_addr = {[0:1279], [1450:2047]};
  }
  waddr10Xpush: cross waddr10, push;
endgroup

covergroup ram_w11_cvg @(posedge clk);
  coverpoint push
  { bins write_bin [] = {1024};
    ignore_bins nowrite = {[0:1023],[1025:2047]};
  }
  coverpoint waddr11
  { bins good_addr [] = {[1536:1722]};
    ignore_bins bad_addr = {[0:1535], [1723:2047]};
  }
  waddr11Xpush: cross waddr11, push;
endgroup

covergroup ram_read_cvg @(posedge clk);
  coverpoint ram_re
  { bins read = {1};
    ignore_bins na = {0};
  }
  coverpoint raddr1
  { bins good_addr [] = {[0:16]};
    ignore_bins bad_addr = {[17:2047]};
  }
  coverpoint raddr2
  { bins good_addr [] = {[64:97]};
    ignore_bins bad_addr = {[0:63], [98:2047]};
  }
  coverpoint raddr3
  { bins good_addr [] = {[128:178]};
    ignore_bins bad_addr = {[0:127], [179:2047]};
  }
  coverpoint raddr4
  { bins good_addr [] = {[256:323]};
    ignore_bins bad_addr = {[0:255], [324:2047]};
  }
  coverpoint raddr5
  { bins good_addr [] = {[384:468]};
    ignore_bins bad_addr = {[0:383], [469:2047]};
  }
  coverpoint raddr6
  { bins good_addr [] = {[512:613]};
    ignore_bins bad_addr = {[0:511], [614:2047]};
  }
  coverpoint raddr7
  { bins good_addr [] = {[640:758]};
    ignore_bins bad_addr = {[0:639], [759:2047]};
  }
  coverpoint raddr8
  { bins good_addr [] = {[768:903]};
    ignore_bins bad_addr = {[0:767], [904:2047]};
  }
  coverpoint raddr9
  { bins good_addr [] = {[1024:1176]};
    ignore_bins bad_addr = {[0:1023], [1177:2047]};
  }
  coverpoint raddr10
  { bins good_addr [] = {[1280:1449]};
    ignore_bins bad_addr = {[0:1279], [1450:2047]};
  }
  coverpoint raddr11
  { bins good_addr [] = {[1536:1722]};
    ignore_bins bad_addr = {[0:1535], [1723:2047]};
  }

  raddr1Xpush: cross raddr1, ram_re;
  raddr2Xpush: cross raddr2, ram_re;
  raddr3Xpush: cross raddr3, ram_re;
  raddr4Xpush: cross raddr4, ram_re;
  raddr5Xpush: cross raddr5, ram_re;
  raddr6Xpush: cross raddr6, ram_re;
  raddr7Xpush: cross raddr7, ram_re;
  raddr8Xpush: cross raddr8, ram_re;
  raddr9Xpush: cross raddr9, ram_re;
  raddr10Xpush: cross raddr10, ram_re;
  raddr11Xpush: cross raddr11, ram_re;

endgroup

ram_w1_cvg ram_w1_cvg_c1 = new;
ram_w2_cvg ram_w2_cvg_c1 = new;
ram_w3_cvg ram_w3_cvg_c1 = new;
ram_w4_cvg ram_w4_cvg_c1 = new;
ram_w5_cvg ram_w5_cvg_c1 = new;
ram_w6_cvg ram_w6_cvg_c1 = new;
ram_w7_cvg ram_w7_cvg_c1 = new;
ram_w8_cvg ram_w8_cvg_c1 = new;
ram_w9_cvg ram_w9_cvg_c1 = new;
ram_w10_cvg ram_w10_cvg_c1 = new;
ram_w11_cvg ram_w11_cvg_c1 = new;
ram_read_cvg ram_read_cvg_c1 = new;

assign
  ram_we = |push ? 1'b1 : 1'b0;

// write address mux
assign
  addra = (sel == 4'h0) ? waddr1 :
          (sel == 4'h1) ? waddr2 :
          (sel == 4'h2) ? waddr3 :
          (sel == 4'h3) ? waddr4 :
          (sel == 4'h4) ? waddr5 :
          (sel == 4'h5) ? waddr6 :
          (sel == 4'h6) ? waddr7 :
          (sel == 4'h7) ? waddr8 :
          (sel == 4'h8) ? waddr9 :
          (sel == 4'h9) ? waddr10 : waddr11;

// read address mux
assign
  addrb = (sel == 4'h0) ? raddr1 :
          (sel == 4'h1) ? raddr2 :
          (sel == 4'h2) ? raddr3 :
          (sel == 4'h3) ? raddr4 :
          (sel == 4'h4) ? raddr5 :
          (sel == 4'h5) ? raddr6 :
          (sel == 4'h6) ? raddr7 :
          (sel == 4'h7) ? raddr8 :
          (sel == 4'h8) ? raddr9 :
          (sel == 4'h9) ? raddr10 : raddr11;

// increment the write address pointers if they are selected
// and there is a write to the ram. Check for max address
// before incrementing. If max address is reached then reset
// address to initial value.

always @(posedge clk or negedge reset_n)
if (!reset_n)
  begin
    waddr1  <= 11'd0;
    waddr2  <= 11'd64;
    waddr3  <= 11'd128;
    waddr4  <= 11'd256;
    waddr5  <= 11'd384;
    waddr6  <= 11'd512;
    waddr7  <= 11'd640;
    waddr8  <= 11'd768;
    waddr9  <= 11'd1024;
    waddr10 <= 11'd1280;
    waddr11 <= 11'd1536;
  end
else if (|push)
  case (sel)
    4'h0:
      if (waddr1 == 11'd16)
        waddr1 <= 11'd0;
      else
        waddr1 <= waddr1 + 11'd1;
    4'h1:
      if (waddr2 == 11'd97)
        waddr2 <= 11'd64;
      else
        waddr2 <= waddr2 + 11'd1;
    4'h2:
      if (waddr3 == 11'd178)
        waddr3 <= 11'd128;
      else
        waddr3 <= waddr3 + 11'd1;
    4'h3:
      if (waddr4 == 11'd323)
        waddr4 <= 11'd256;
      else
        waddr4 <= waddr4 + 11'd1;
    4'h4:
      if (waddr5 == 11'd468)
        waddr5 <= 11'd384;
      else
        waddr5 <= waddr5 + 11'd1;
    4'h5:
      if (waddr6 == 11'd613)
        waddr6 <= 11'd512;
      else
        waddr6 <= waddr6 + 11'd1;
    4'h6:
      if (waddr7 == 11'd758)
        waddr7 <= 11'd640;
      else
        waddr7 <= waddr7 + 11'd1;
    4'h7:
      if (waddr8 == 11'd903)
        waddr8 <= 11'd768;
      else
        waddr8 <= waddr8 + 11'd1;
    4'h8:
      if (waddr9 == 11'd1176)
        waddr9 <= 11'd1024;
      else
        waddr9 <= waddr9 + 11'd1;
    4'h9:
      if (waddr10 == 11'd1449)
        waddr10 <= 11'd1280;
      else
        waddr10 <= waddr10 + 11'd1;
    default:
      if (BUG == 0)
        if (waddr11 == 11'd1722)
          waddr11 <= 11'd1536;
        else
          waddr11 <= waddr11 + 11'd1;
      else
        if (waddr11 == 11'd1724)
          waddr11 <= 11'd1536;
        else
          waddr11 <= waddr11 + 11'd1;
  endcase

// the read address pointers needs to increment each
// time the write pointers are incremented. The ram read
// are initialized to the write address plus 1. Check for
// the max address before incrementing. If max address is
// reached then reset address to initial value.

always @(posedge clk or negedge reset_n)
if (!reset_n)
  begin
    raddr1  <= 11'd0;
    raddr2  <= 11'd64;
    raddr3  <= 11'd128;
    raddr4  <= 11'd256;
    raddr5  <= 11'd384;
    raddr6  <= 11'd512;
    raddr7  <= 11'd640;
    raddr8  <= 11'd768;
    raddr9  <= 11'd1024;
    raddr10 <= 11'd1280;
    raddr11 <= 11'd1536;
  end
else if (|push)
  case (sel)
    4'h0:
      if (raddr1 == 11'd16)
        raddr1 <= 11'd0;
      else
        raddr1 <= raddr1 + 11'd1;
    4'h1:
      if (raddr2 == 11'd97)
        raddr2 <= 11'd64;
      else
        raddr2 <= raddr2 + 11'd1;
    4'h2:
      if (raddr3 == 11'd178)
        raddr3 <= 11'd128;
      else
        raddr3 <= raddr3 + 11'd1;
    4'h3:
      if (raddr4 == 11'd323)
        raddr4 <= 11'd256;
      else
        raddr4 <= raddr4 + 11'd1;
    4'h4:
      if (raddr5 == 11'd468)
        raddr5 <= 11'd384;
      else
        raddr5 <= raddr5 + 11'd1;
    4'h5:
      if (raddr6 == 11'd613)
        raddr6 <= 11'd512;
      else
        raddr6 <= raddr6 + 11'd1;
    4'h6:
      if (raddr7 == 11'd758)
        raddr7 <= 11'd640;
      else
        raddr7 <= raddr7 + 11'd1;
    4'h7:
      if (raddr8 == 11'd903)
        raddr8 <= 11'd768;
      else
        raddr8 <= raddr8 + 11'd1;
    4'h8:
      if (raddr9 == 11'd1176)
        raddr9 <= 11'd1024;
      else
        raddr9 <= raddr9 + 11'd1;
    4'h9:
      if (raddr10 == 11'd1449)
        raddr10 <= 11'd1280;
      else
        raddr10 <= raddr10 + 11'd1;
    default:
        if (raddr11 == 11'd1722)
          raddr11 <= 11'd1536;
        else
          raddr11 <= raddr11 + 11'd1;
  endcase

ram2p_2kx8 ram_block (
  .wclk(clk),
  .din(din),
  .waddr(addra),
  .we(ram_we),
  .re(ram_re),
  .rclk(clk),
  .raddr(addrb),
  .dout(dout)
  );

endmodule
