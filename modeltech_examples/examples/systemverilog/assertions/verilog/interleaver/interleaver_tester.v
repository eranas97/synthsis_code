module interleaver_tester #(parameter RUNFC = 1'b0, BUG = 1, WIDTH = 8) ();

`define COMB_DLY
`define CLK2Q_DLY

   reg  reset,clk;
   reg  [WIDTH-1:0] upstream_data;
   wire  [WIDTH-1:0] downstream_data;
   reg  [WIDTH-1:0] expected_data;
   wire [WIDTH-1:0] cmp_fifo_data;
   reg  cmp_fifo_push;
   wire cmp_fifo_pop;
   wire /*upstream_rdy,*/upstream_acpt,downstream_acpt,downstream_rdy;
   reg upstream_rdy = 0;
   reg new_acpt = 0;
`ifdef USE_SV
   logic [WIDTH-1:0] new_data = 8'h00;
`else
   reg [WIDTH-1:0] new_data = 8'h00;
`endif

   reg  [WIDTH-1:0] pipe_reg [0:1121];

   reg  [WIDTH:0] up_hs_less10_cnt = {9{1'b0}};

  // Check RTL do with behavior model
  property data_delay_chk;
  @(posedge clk) (downstream_rdy && downstream_acpt) |->  cmp_fifo_data === downstream_data;
  endproperty

  assert property(data_delay_chk);

  // Check for upstream rdy acpt handshake
  property hs_chk (rdy, acpt);
    @(posedge clk) rdy |-> acpt[->1];
  endproperty

  assert property(hs_chk (upstream_rdy, upstream_acpt));
  assert property(hs_chk (downstream_rdy, downstream_acpt));

  property data_hold_chk (rdy, acpt, data);
    @(posedge clk) (rdy & !acpt) |=> $past(data,1) === data;
  endproperty

  assert property(data_hold_chk (upstream_rdy, upstream_acpt, upstream_data));
  assert property(data_hold_chk (downstream_rdy, downstream_acpt, downstream_data));


  // sequence to detect rdy/acpt handshake stalled ten cycles or less
  sequence  s_hs_less_10 (rdy, acpt);
    @(posedge clk) $rose(rdy & !acpt) ##0 (rdy &!acpt)[*0:10] ##1 (rdy & acpt);
  endsequence

  // sequence to detect rdy/acpt handshake stalled 11 cycles or more
  sequence  s_hs_more_10 (rdy, acpt);
    @(posedge clk) $rose(rdy & !acpt) ##0 (rdy &!acpt)[*11:$] ##1 rdy & acpt;
  endsequence

  cover property (s_hs_more_10(upstream_rdy, upstream_acpt));
  cover property (s_hs_less_10(upstream_rdy, upstream_acpt))
  case (RUNFC)
    1'b0:
      up_hs_less10_cnt <= {9{1'b0}};
    1'b1:
        if (up_hs_less10_cnt == 9'b100000000)
          up_hs_less10_cnt <= {9{1'b0}};
        else
         up_hs_less10_cnt <= up_hs_less10_cnt + 1;
   endcase
  cover property (s_hs_less_10(downstream_rdy, downstream_acpt));
  cover property (s_hs_more_10(downstream_rdy, downstream_acpt));

initial
begin
  clk=1'b0;
  reset = 1'b0;
  #100 reset = 1'b1;
end

always
  #5 clk = ~clk;

interleaver #(.BUG(BUG)) interleaver1 (
   .clk(clk),
   .reset_n(reset),
   .di_rdy(upstream_rdy),
   .di_acpt(upstream_acpt),
   .di_data(upstream_data),
   .do_rdy(downstream_rdy),
   .do_acpt(downstream_acpt),
   .do_data(downstream_data),
   .enable(1'b1));

fifo #(.DEPTH(64),.SIZE(6),.WIDTH(WIDTH)) cmp_fifo (
   .clk(clk),
   .reset_n(reset),
   .din(expected_data),
   .push(cmp_fifo_push),
   .pop(cmp_fifo_pop),
   .dout(cmp_fifo_data));

integer i = 0, j = 0; 

`ifdef USE_SV
`else
reg [31:0] up_rand_gen;
`endif

always @(posedge clk or negedge reset)
if (!reset)
  begin
    upstream_rdy <= 1'b0;
    upstream_data <= 8'h00;
  end
else
  begin
    if (upstream_rdy & upstream_acpt)
      upstream_rdy <= 0;
    if (!upstream_rdy)
`ifdef USE_SV
      randcase
        50: 
          begin
            upstream_rdy <= 1;
            if (i == 0)
              if (j == 0)
                upstream_data <= 8'hb8;
              else
                upstream_data <= 8'h47;
            else
              upstream_data = $urandom;
            if (i == 203)
              begin
                i = 0;
                if (j == 7)
                  j = 0;
                else
                  j += 1;
              end
            else 
              i += 1;
          end
        50:
          begin
            upstream_rdy <= 0;
            upstream_data <= 8'h00;
          end
      endcase
`else
      begin
        up_rand_gen = $random;
        if (up_rand_gen[3:0] >= 8)
          begin
            upstream_rdy <= 1;
            if (i == 0)
              if (j == 0)
                upstream_data <= 8'hb8;
              else
                upstream_data <= 8'h47;
            else
              upstream_data <= up_rand_gen[31:24];
            if (i == 203)
              begin
                i = 0;
                if (j == 7)
                  j = 0;
                else
                  j = j + 1;
              end
            else
              i = i + 1;
          end
        else
          begin
            upstream_rdy <= 0;
            upstream_data <= 8'h00;
          end
      end
`endif
  end


assign `COMB_DLY
  downstream_acpt = new_acpt;           

`ifdef USE_SV
`else
reg [31:0] dwn_rand_gen;
`endif

always @(posedge clk or negedge reset)
if (!reset)
  new_acpt <= 1'b0;
else
  begin
    if (downstream_rdy && downstream_acpt)
      new_acpt <= 0;
    if (!new_acpt)
      if(up_hs_less10_cnt < 9'b010000000)
`ifdef USE_SV
        randcase
          50: new_acpt <= 1;
          50: new_acpt <= 0;
        endcase
      else
        randcase
          1: new_acpt <= 1;
          10: new_acpt <= 0;
        endcase
`else
          begin
            dwn_rand_gen = $random;
            if (dwn_rand_gen[3:0] >= 4'h8)
              new_acpt <= 1;
            else
              new_acpt <= 0;
          end
        else
          begin
            dwn_rand_gen = $random;
            if (dwn_rand_gen[3:0] >= 4'he)
              new_acpt <= 1;
            else
              new_acpt <= 0;
          end

`endif
  end

assign `COMB_DLY
  cmp_fifo_pop = downstream_rdy & downstream_acpt;

integer k, m;

always @(posedge clk or negedge reset)
if (!reset)
  begin
    k = 0;
    cmp_fifo_push <= 1'b0;
  end
else
  begin
    if (downstream_rdy & downstream_acpt)
`ifdef USE_SV
        assert (cmp_fifo_data === downstream_data) else 
          begin
            $display("CMP FIFO DATA = %h RTL MODEL DATA = %h", cmp_fifo_data,downstream_data);
            $display("Data Miscompare ERROR at time", $time);
            $stop;
          end
`else
      if (cmp_fifo_data != downstream_data)
        begin
          $display("CMP FIFO DATA = %h RTL MODEL DATA = %h", cmp_fifo_data,downstream_data);
          $display("Data Miscompare ERROR at time", $time);
          $stop;
        end
`endif
    if (upstream_rdy & upstream_acpt)
      begin
        cmp_fifo_push <=  1'b1;
        case (k)
          0: expected_data <= upstream_data;
          1:
            begin
              expected_data =  pipe_reg[16];
              `ifdef USE_SV
              for (m=16; m>0; m--)
              `else
              for (m=16; m>0; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[0] <= upstream_data;
            end
          2:
            begin
              expected_data <= pipe_reg[50];
              `ifdef USE_SV
              for (m=50; m>17; m--)
              `else
              for (m=50; m>17; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[17] <= upstream_data;
            end
          3:
            begin
              expected_data <= pipe_reg[101];
              `ifdef USE_SV
              for (m=101; m>51; m--)
              `else
              for (m=101; m>51; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[51] <= upstream_data;
            end
          4:
            begin
              expected_data <= pipe_reg[169];
              `ifdef USE_SV
              for (m=169; m>102; m--)
              `else
              for (m=169; m>102; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[102] <= upstream_data;
            end
          5:
            begin
              expected_data <= pipe_reg[254];
              `ifdef USE_SV
              for (m=254; m>170; m--)
              `else
              for (m=254; m>170; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[170] <= upstream_data;
            end
          6:
            begin
              expected_data <= pipe_reg[356];
              `ifdef USE_SV
              for (m=356; m>255; m--)
              `else
              for (m=356; m>255; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[255] <= upstream_data;
            end
          7:
            begin
              expected_data <= pipe_reg[475];
              `ifdef USE_SV
              for (m=475; m>357; m--)
              `else
              for (m=475; m>357; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[357] <= upstream_data;
            end
          8:
            begin
              expected_data <= pipe_reg[611];
              `ifdef USE_SV
              for (m=611; m>476; m--)
              `else
              for (m=611; m>476; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[476] <= upstream_data;
            end
          9:
            begin
              expected_data <= pipe_reg[764];
              `ifdef USE_SV
              for (m=764; m>612; m--)
              `else
              for (m=764; m>612; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[612] <= upstream_data;
            end
          10:
            begin
              expected_data <= pipe_reg[934];
              `ifdef USE_SV
              for (m=934; m>765; m--)
              `else
              for (m=934; m>765; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[765] <= upstream_data;
            end
          11:
            begin
              expected_data <= pipe_reg[1121];
              `ifdef USE_SV
              for (m=1121; m>935; m--)
              `else
              for (m=1121; m>935; m=m-1)
              `endif
                pipe_reg[m] <= pipe_reg[m-1];
              pipe_reg[935] <= upstream_data;
            end
          default:
            begin
              $display("Reached the Default case in ERROR at time", $time);
              $stop;
            end
        endcase
        if (k == 11)
          k = 0;
        else
          k = k + 1;
      end
    else
      cmp_fifo_push <= 1'b0;
  end

endmodule
                 
