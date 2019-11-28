module fifo_shift_ram #(parameter BUG=0) (
  input clk, reset_n, ram_re,
  input [10:0] push,
  input [7:0] din,
  input [3:0] sel,
  output [7:0] dout
  );

wire [10:0] addra;
wire [10:0] addrb;
reg [10:0] waddr [11:1];
reg [10:0] raddr [11:1];
reg [10:0] lorange [11:1] = {1536,1280,1024,768,640,512,384,256,128,64,0};
reg [10:0] hirange [11:1] = {1722,1449,1176,903,758,613,468,323,178,97,16};
wire ram_we;

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


// Default assertion clock
// psl default clock = (posedge clk);

// Verify that only one level of the RAM is written at a time
// psl property push_mutex_check = always {ram_we} |-> { onehot(push); !ram_we};
// psl assert push_mutex_check;

// Verify that the proper level RAM address is selected
// and the RAM address is within the acceptable range during a write
// and post incremented write address is still in acceptable range

// pl property ram_write_check = forall i in {1:11} : always
// {push[i-1]} |-> {addra == waddr[i] && waddr[i] >= lorange[i] && waddr[i] <= hirange[i];
// !push[i-1] && waddr[i] >= lorange[i] && waddr[i] <= hirange[i]};

// pl assert ram_write_check;

// psl property ram_write_check (boolean we, wadd_eq_ram_add, wadd_lowrange, wadd_higrange) =
// always {we} |-> {wadd_eq_ram_add && wadd_lowrange && wadd_higrange; !we && wadd_lowrange && wadd_higrange};

// %for i in 1 .. 11 do
// psl assert ram_write_check (push[i-1],(addra == waddr[i]),(waddr[i] >= lorange[i],(waddr[i] <= hirange[i]));
// %end

// pl assert ram_write_check (push[0],  (addra == waddr1),  (waddr1 >= 11'd0),     (waddr1 <= 11'd16));
// pl assert ram_write_check (push[1],  (addra == waddr2),  (waddr2 >= 11'd64),    (waddr2 <= 11'd97));
// pl assert ram_write_check (push[2],  (addra == waddr3),  (waddr3 >= 11'd128),   (waddr3 <= 11'd178));
// pl assert ram_write_check (push[3],  (addra == waddr4),  (waddr4 >= 11'd256),   (waddr4 <= 11'd323));
// pl assert ram_write_check (push[4],  (addra == waddr5),  (waddr5 >= 11'd384),   (waddr5 <= 11'd468));
// pl assert ram_write_check (push[5],  (addra == waddr6),  (waddr6 >= 11'd512),   (waddr6 <= 11'd613));
// pl assert ram_write_check (push[6],  (addra == waddr7),  (waddr7 >= 11'd640),   (waddr7 <= 11'd758));
// pl assert ram_write_check (push[7],  (addra == waddr8),  (waddr8 >= 11'd768),   (waddr8 <= 11'd903));
// pl assert ram_write_check (push[8],  (addra == waddr9),  (waddr9 >= 11'd1024),  (waddr9 <= 11'd1176));
// pl assert ram_write_check (push[9],  (addra == waddr10), (waddr10 >= 11'd1280), (waddr10 <= 11'd1449));
// pl assert ram_write_check (push[10], (addra == waddr11), (waddr11 >= 11'd1536), (waddr11 <= 11'd1722));


// psl property ram_read_check = forall j in {1:11} : always
// {ram_re && addrb == raddr[j]} |-> {raddr[j] >= lorange[j] && raddr[j] <= hirange[j]; !ram_re};

// psl assert ram_read_check;

// Verify that the proper level RAM address is selected
// and the RAM address is within the acceptable range during a read
// pl property ram_read_check (boolean rden, radd_eq_ram_add, radd_lowrange, radd_highrange) =
// always {(rden && radd_eq_ram_add)} |-> {radd_lowrange && radd_highrange; !rden};

// pl assert ram_read_check (ram_re, (addrb == raddr1),  (raddr1 >= 11'd0),     (raddr1 <= 11'd16));
// pl assert ram_read_check (ram_re, (addrb == raddr2),  (raddr2 >= 11'd64),    (raddr2 <= 11'd97));
// pl assert ram_read_check (ram_re, (addrb == raddr3),  (raddr3 >= 11'd128),   (raddr3 <= 11'd178));
// pl assert ram_read_check (ram_re, (addrb == raddr4),  (raddr4 >= 11'd256),   (raddr4 <= 11'd323));
// pl assert ram_read_check (ram_re, (addrb == raddr5),  (raddr5 >= 11'd384),   (raddr5 <= 11'd468));
// pl assert ram_read_check (ram_re, (addrb == raddr6),  (raddr6 >= 11'd512),   (raddr6 <= 11'd613));
// pl assert ram_read_check (ram_re, (addrb == raddr7),  (raddr7 >= 11'd640),   (raddr7 <= 11'd758));
// pl assert ram_read_check (ram_re, (addrb == raddr8),  (raddr8 >= 11'd768),   (raddr8 <= 11'd903));
// pl assert ram_read_check (ram_re, (addrb == raddr9),  (raddr9 >= 11'd1024),  (raddr9 <= 11'd1176));
// pl assert ram_read_check (ram_re, (addrb == raddr10), (raddr10 >= 11'd1280), (raddr10 <= 11'd1449));
// pl assert ram_read_check (ram_re, (addrb == raddr11), (raddr11 >= 11'd1536), (raddr11 <= 11'd1722));


assign
  ram_we = |push ? 1'b1 : 1'b0;

// write address mux
assign
  addra = (sel == 4'h0) ? waddr[1] :
          (sel == 4'h1) ? waddr[2] :
          (sel == 4'h2) ? waddr[3] :
          (sel == 4'h3) ? waddr[4] :
          (sel == 4'h4) ? waddr[5] :
          (sel == 4'h5) ? waddr[6] :
          (sel == 4'h6) ? waddr[7] :
          (sel == 4'h7) ? waddr[8] :
          (sel == 4'h8) ? waddr[9] :
          (sel == 4'h9) ? waddr[10] : waddr[11];

// read address mux
assign
  addrb = (sel == 4'h0) ? raddr[1] :
          (sel == 4'h1) ? raddr[2] :
          (sel == 4'h2) ? raddr[3] :
          (sel == 4'h3) ? raddr[4] :
          (sel == 4'h4) ? raddr[5] :
          (sel == 4'h5) ? raddr[6] :
          (sel == 4'h6) ? raddr[7] :
          (sel == 4'h7) ? raddr[8] :
          (sel == 4'h8) ? raddr[9] :
          (sel == 4'h9) ? raddr[10] : raddr[11];

// increment the write address pointers if they are selected
// and there is a write to the ram. Check for max address
// before incrementing. If max address is reached then reset
// address to initial value.

always @(posedge clk or negedge reset_n)
if (!reset_n)
  begin
    waddr[1]  <= 11'd0;
    waddr[2]  <= 11'd64;
    waddr[3]  <= 11'd128;
    waddr[4]  <= 11'd256;
    waddr[5]  <= 11'd384;
    waddr[6]  <= 11'd512;
    waddr[7]  <= 11'd640;
    waddr[8]  <= 11'd768;
    waddr[9]  <= 11'd1024;
    waddr[10] <= 11'd1280;
    waddr[11] <= 11'd1536;
  end
else if (|push)
  case (sel)
    4'h0:
      if (waddr[1] == 11'd16)
        waddr[1] <= 11'd0;
      else
        waddr[1] <= waddr[1] + 11'd1;
    4'h1:
      if (waddr[2] == 11'd97)
        waddr[2] <= 11'd64;
      else
        waddr[2] <= waddr[2] + 11'd1;
    4'h2:
      if (waddr[3] == 11'd178)
        waddr[3] <= 11'd128;
      else
        waddr[3] <= waddr[3] + 11'd1;
    4'h3:
      if (waddr[4] == 11'd323)
        waddr[4] <= 11'd256;
      else
        waddr[4] <= waddr[4] + 11'd1;
    4'h4:
      if (waddr[5] == 11'd468)
        waddr[5] <= 11'd384;
      else
        waddr[5] <= waddr[5] + 11'd1;
    4'h5:
      if (waddr[6] == 11'd613)
        waddr[6] <= 11'd512;
      else
        waddr[6] <= waddr[6] + 11'd1;
    4'h6:
      if (waddr[7] == 11'd758)
        waddr[7] <= 11'd640;
      else
        waddr[7] <= waddr[7] + 11'd1;
    4'h7:
      if (waddr[8] == 11'd903)
        waddr[8] <= 11'd768;
      else
        waddr[8] <= waddr[8] + 11'd1;
    4'h8:
      if (waddr[9] == 11'd1176)
        waddr[9] <= 11'd1024;
      else
        waddr[9] <= waddr[9] + 11'd1;
    4'h9:
      if (waddr[10] == 11'd1449)
        waddr[10] <= 11'd1280;
      else
        waddr[10] <= waddr[10] + 11'd1;
    default:
      if (BUG == 0)
        if (waddr[11] == 11'd1722)
          waddr[11] <= 11'd1536;
        else
          waddr[11] <= waddr[11] + 11'd1;
      else
        if (waddr[11] == 11'd1724)
          waddr[11] <= 11'd1536;
        else
          waddr[11] <= waddr[11] + 11'd1;
  endcase

// the read address pointers needs to increment each
// time the write pointers are incremented. The ram read
// are initialized to the write address plus 1. Check for
// the max address before incrementing. If max address is
// reached then reset address to initial value.

always @(posedge clk or negedge reset_n)
if (!reset_n)
  begin
    raddr[1]  <= 11'd0;
    raddr[2]  <= 11'd64;
    raddr[3]  <= 11'd128;
    raddr[4]  <= 11'd256;
    raddr[5]  <= 11'd384;
    raddr[6]  <= 11'd512;
    raddr[7]  <= 11'd640;
    raddr[8]  <= 11'd768;
    raddr[9]  <= 11'd1024;
    raddr[10] <= 11'd1280;
    raddr[11] <= 11'd1536;
  end
else if (|push)
  case (sel)
    4'h0:
      if (raddr[1] == 11'd16)
        raddr[1] <= 11'd0;
      else
        raddr[1] <= raddr[1] + 11'd1;
    4'h1:
      if (raddr[2] == 11'd97)
        raddr[2] <= 11'd64;
      else
        raddr[2] <= raddr[2] + 11'd1;
    4'h2:
      if (raddr[3] == 11'd178)
        raddr[3] <= 11'd128;
      else
        raddr[3] <= raddr[3] + 11'd1;
    4'h3:
      if (raddr[4] == 11'd323)
        raddr[4] <= 11'd256;
      else
        raddr[4] <= raddr[4] + 11'd1;
    4'h4:
      if (raddr[5] == 11'd468)
        raddr[5] <= 11'd384;
      else
        raddr[5] <= raddr[5] + 11'd1;
    4'h5:
      if (raddr[6] == 11'd613)
        raddr[6] <= 11'd512;
      else
        raddr[6] <= raddr[6] + 11'd1;
    4'h6:
      if (raddr[7] == 11'd758)
        raddr[7] <= 11'd640;
      else
        raddr[7] <= raddr[7] + 11'd1;
    4'h7:
      if (raddr[8] == 11'd903)
        raddr[8] <= 11'd768;
      else
        raddr[8] <= raddr[8] + 11'd1;
    4'h8:
      if (raddr[9] == 11'd1176)
        raddr[9] <= 11'd1024;
      else
        raddr[9] <= raddr[9] + 11'd1;
    4'h9:
      if (raddr[10] == 11'd1449)
        raddr[10] <= 11'd1280;
      else
        raddr[10] <= raddr[10] + 11'd1;
    default:
        if (raddr[11] == 11'd1722)
          raddr[11] <= 11'd1536;
        else
          raddr[11] <= raddr[11] + 11'd1;
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
