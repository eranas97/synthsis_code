module sva_top_props #(parameter RUNFC = 0) (
   input clk,
   upstream_rdy,
   upstream_acpt,
   downstream_rdy,
   downstream_acpt,
   input [7:0] upstream_data,
   downstream_data,
   cmp_fifo_data
);

 reg [8:0] up_hs_less10_cnt = {9{1'b0}};

// property to check behavioral model equals RTL model
  property data_delay_chk;
  @(posedge clk) (downstream_rdy && downstream_acpt) |->  cmp_fifo_data === downstream_data;
  endproperty

  assert property(data_delay_chk);

// property to check rdy acpt handshakes
  property hs_chk (rdy, acpt);
    @(posedge clk) rdy |-> ##[0:$] acpt;
  endproperty

  assert property(hs_chk (upstream_rdy, upstream_acpt));
  assert property(hs_chk (downstream_rdy, downstream_acpt));

// property to check data is held if acpt is not accepted
  property data_hold_chk (rdy, acpt, data);
    @(posedge clk) (rdy & !acpt) |=> $past(data,1) === data;
  endproperty

  assert property(data_hold_chk (upstream_rdy, upstream_acpt, upstream_data));
  assert property(data_hold_chk (downstream_rdy, downstream_acpt, downstream_data));

 sequence  s_hs_less_10 (rdy, acpt);
    @(posedge clk) $rose(rdy & !acpt) ##0 (rdy &!acpt)[*0:10] ##1 (rdy & acpt);
  endsequence

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


endmodule
