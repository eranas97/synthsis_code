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

// Default assertion clock
// psl default clock = (posedge clk);

// Verify that only one level of the RAM is written at a time
// psl property push_mutex_check = always {ram_we} |-> { onehot(push); !ram_we};
// psl assert push_mutex_check;

// Verify that the proper level RAM address is selected
// and the RAM address is within the acceptable range during a write
// and post incremented write address is still in acceptable range

// psl property ram_write_check (boolean we, wadd_eq_ram_add, wadd_lowrange, wadd_higrange) =
// always {we} |-> {wadd_eq_ram_add && wadd_lowrange && wadd_higrange; !we && wadd_lowrange && wadd_higrange};


// psl assert ram_write_check (push[0],  (addra == waddr1),  (waddr1 >= 11'd0),     (waddr1 <= 11'd16));
// psl assert ram_write_check (push[1],  (addra == waddr2),  (waddr2 >= 11'd64),    (waddr2 <= 11'd97));
// psl assert ram_write_check (push[2],  (addra == waddr3),  (waddr3 >= 11'd128),   (waddr3 <= 11'd178));
// psl assert ram_write_check (push[3],  (addra == waddr4),  (waddr4 >= 11'd256),   (waddr4 <= 11'd323));
// psl assert ram_write_check (push[4],  (addra == waddr5),  (waddr5 >= 11'd384),   (waddr5 <= 11'd468));
// psl assert ram_write_check (push[5],  (addra == waddr6),  (waddr6 >= 11'd512),   (waddr6 <= 11'd613));
// psl assert ram_write_check (push[6],  (addra == waddr7),  (waddr7 >= 11'd640),   (waddr7 <= 11'd758));
// psl assert ram_write_check (push[7],  (addra == waddr8),  (waddr8 >= 11'd768),   (waddr8 <= 11'd903));
// psl assert ram_write_check (push[8],  (addra == waddr9),  (waddr9 >= 11'd1024),  (waddr9 <= 11'd1176));
// psl assert ram_write_check (push[9],  (addra == waddr10), (waddr10 >= 11'd1280), (waddr10 <= 11'd1449));
// psl assert ram_write_check (push[10], (addra == waddr11), (waddr11 >= 11'd1536), (waddr11 <= 11'd1722));


// Verify that the proper level RAM address is selected
// and the RAM address is within the acceptable range during a read
// psl property ram_read_check (boolean rden, radd_eq_ram_add, radd_lowrange, radd_highrange) =
// always {(rden && radd_eq_ram_add)} |-> {radd_lowrange && radd_highrange; !rden};

// psl assert ram_read_check (ram_re, (addrb == raddr1),  (raddr1 >= 11'd0),     (raddr1 <= 11'd16));
// psl assert ram_read_check (ram_re, (addrb == raddr2),  (raddr2 >= 11'd64),    (raddr2 <= 11'd97));
// psl assert ram_read_check (ram_re, (addrb == raddr3),  (raddr3 >= 11'd128),   (raddr3 <= 11'd178));
// psl assert ram_read_check (ram_re, (addrb == raddr4),  (raddr4 >= 11'd256),   (raddr4 <= 11'd323));
// psl assert ram_read_check (ram_re, (addrb == raddr5),  (raddr5 >= 11'd384),   (raddr5 <= 11'd468));
// psl assert ram_read_check (ram_re, (addrb == raddr6),  (raddr6 >= 11'd512),   (raddr6 <= 11'd613));
// psl assert ram_read_check (ram_re, (addrb == raddr7),  (raddr7 >= 11'd640),   (raddr7 <= 11'd758));
// psl assert ram_read_check (ram_re, (addrb == raddr8),  (raddr8 >= 11'd768),   (raddr8 <= 11'd903));
// psl assert ram_read_check (ram_re, (addrb == raddr9),  (raddr9 >= 11'd1024),  (raddr9 <= 11'd1176));
// psl assert ram_read_check (ram_re, (addrb == raddr10), (raddr10 >= 11'd1280), (raddr10 <= 11'd1449));
// psl assert ram_read_check (ram_re, (addrb == raddr11), (raddr11 >= 11'd1536), (raddr11 <= 11'd1722));


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
