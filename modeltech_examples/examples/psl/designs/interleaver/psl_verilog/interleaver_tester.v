module interleaver_tester #(parameter RUNFC = 1'b0, BUG = 1, WIDTH = 8) ();

`define COMB_DLY #1
`define CLK2Q_DLY #2

   reg  reset,clk;
   wire  [WIDTH-1:0] upstream_data;
   wire  [WIDTH-1:0] downstream_data;
   reg  [WIDTH-1:0] expected_data;
   wire [WIDTH-1:0] cmp_fifo_data;
   reg  cmp_fifo_push;
   wire cmp_fifo_pop;
   wire upstream_rdy,upstream_acpt,downstream_acpt,downstream_rdy;
   reg new_rdy = 0;
   reg new_acpt = 0;
`ifdef USE_SV
   logic [WIDTH-1:0] new_data = 8'h00;
`else
   reg [WIDTH-1:0] new_data = 8'h00;
`endif
   //reg up_hs_less10_hit = 0;

   reg  [WIDTH-1:0] pipe_reg [0:1121];

   reg  [WIDTH:0] up_hs_less10_cnt = {9{1'b0}};

  // psl default clock = (posedge clk);

  // Check RTL do with behavior model
  // psl property data_delay_check = always {downstream_rdy && downstream_acpt} |->
  // { cmp_fifo_data === downstream_data };
  // psl assert data_delay_check;

  // Check for upstream rdy acpt handshake
  // psl property up_hs_check = always (upstream_rdy -> eventually!( upstream_acpt));
  // psl assert up_hs_check;

  // Check for downstream rdy acpt handshake
  // psl property dwn_hs_check = always (downstream_rdy -> eventually! (downstream_acpt));
  // psl assert dwn_hs_check;

  // Check for upstream data to hold if acpt de-asserted
  // psl property up_data_hold_check = always {upstream_rdy && !upstream_acpt} |=>
  //   {upstream_data === prev(upstream_data)};
  // psl assert up_data_hold_check;

  // psl sequence s_no_up_hs_less_10 = {rose(upstream_rdy && !upstream_acpt);
  //                                   (upstream_rdy && !upstream_acpt)[*0:10];
  //                                   (upstream_rdy && upstream_acpt)};

  // psl c_no_up_hs_less_10: cover s_no_up_hs_less_10;

  // psl sequence up_hs_less10_hit = {s_no_up_hs_less_10};

  // psl sequence s_no_up_hs_more_10 = {rose(upstream_rdy && !upstream_acpt);
  //                                   (upstream_rdy && !upstream_acpt)[*11:inf];
  //                                    upstream_rdy && upstream_acpt};

  // psl c_no_up_hs_more_10: cover s_no_up_hs_more_10;

  // Check for downstream data to hold if acpt de-asserted
  // psl property dwn_data_hold_check = always {downstream_rdy && !downstream_acpt} |=>
  //   {downstream_data === prev(downstream_data)};
  // psl assert dwn_data_hold_check;

  // psl sequence s_no_dwn_hs_less_10 = {rose(downstream_rdy && !downstream_acpt);
  //                                   (downstream_rdy && !downstream_acpt)[*0:10];
  //                                    downstream_rdy && downstream_acpt};

  // psl c_no_dwn_hs_less_10: cover s_no_dwn_hs_less_10;

  // psl sequence s_no_dwn_hs_more_10 = {rose(downstream_rdy && !downstream_acpt);
  //                                   (downstream_rdy && !downstream_acpt)[*11:inf];
  //                                    downstream_rdy && downstream_acpt};

  // psl c_no_dwn_hs_more_10: cover s_no_dwn_hs_more_10;


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
   .di(upstream_data),
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

always @(posedge clk or negedge reset)
if (!reset)
  up_hs_less10_cnt <= {9{1'b0}};

else
  case (RUNFC)
    1'b0:
      up_hs_less10_cnt <= {9{1'b0}};
    1'b1:
      if (ended(up_hs_less10_hit))
        if (up_hs_less10_cnt == 9'b100000000)
          up_hs_less10_cnt <= {9{1'b0}};
        else
         up_hs_less10_cnt <= up_hs_less10_cnt + 1;
   endcase

integer i = 0, j = 0; 

assign `COMB_DLY
  upstream_rdy = new_rdy,
  upstream_data = new_data;

`ifdef USE_SV
`else
reg [31:0] up_rand_gen;
`endif

always @(posedge clk or negedge reset)
if (!reset)
  begin
    new_rdy = 1'b0;
    new_data = 8'h00;
  end
else
  begin
    if (upstream_rdy & upstream_acpt)
      new_rdy = 0;
    if (!new_rdy)
`ifdef USE_SV
      randcase
        50: 
          begin
            new_rdy = 1;
            if (i == 0)
              if (j == 0)
                new_data = 8'hb8;
              else
                new_data = 8'h47;
            else
              new_data = $urandom;
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
            new_rdy = 0;
            new_data = 8'h00;
          end
      endcase
`else
      begin
        up_rand_gen = $random;
        if (up_rand_gen[3:0] >= 8)
          begin
            new_rdy = 1;
            if (i == 0)
              if (j == 0)
                new_data = 8'hb8;
              else
                new_data = 8'h47;
            else
              new_data = up_rand_gen[31:24];
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
            new_rdy = 0;
            new_data = 8'h00;
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
  new_acpt = 1'b0;
else
  begin
    if (downstream_rdy && downstream_acpt)
      new_acpt = 0;
    if (!new_acpt)
      if(up_hs_less10_cnt < 9'b010000000)
`ifdef USE_SV
        randcase
          50: new_acpt = 1;
          50: new_acpt = 0;
        endcase
      else
        randcase
          1: new_acpt = 1;
          10: new_acpt = 0;
        endcase
`else
          begin
            dwn_rand_gen = $random;
            if (dwn_rand_gen[3:0] >= 4'h8)
              new_acpt = 1;
            else
              new_acpt = 0;
          end
        else
          begin
            dwn_rand_gen = $random;
            if (dwn_rand_gen[3:0] >= 4'he)
              new_acpt = 1;
            else
              new_acpt = 0;
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
    cmp_fifo_push = 1'b0;
  end
else
  begin
    if (downstream_rdy & downstream_acpt)
        assert (cmp_fifo_data === downstream_data); else 
          begin
            $display("CMP FIFO DATA = %h RTL MODEL DATA = %h", cmp_fifo_data,downstream_data);
            $display("Data Miscompare ERROR at time", $time);
            $stop;
          end
/*
      if (cmp_fifo_data != downstream_data)
        begin
          $display("CMP FIFO DATA = %h RTL MODEL DATA = %h", cmp_fifo_data,downstream_data);
          $display("Data Miscompare ERROR at time", $time);
          $stop;
        end
*/
    if (upstream_rdy & upstream_acpt)
      begin
        cmp_fifo_push =  1'b1;
        case (k)
          0: expected_data = upstream_data;
          1:
            begin
              expected_data =  pipe_reg[16];
              `ifdef USE_SV
              for (m=16; m>0; m--)
              `else
              for (m=16; m>0; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[0] = upstream_data;
            end
          2:
            begin
              expected_data = pipe_reg[50];
              `ifdef USE_SV
              for (m=50; m>17; m--)
              `else
              for (m=50; m>17; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[17] = upstream_data;
            end
          3:
            begin
              expected_data = pipe_reg[101];
              `ifdef USE_SV
              for (m=101; m>51; m--)
              `else
              for (m=101; m>51; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[51] = upstream_data;
            end
          4:
            begin
              expected_data = pipe_reg[169];
              `ifdef USE_SV
              for (m=169; m>102; m--)
              `else
              for (m=169; m>102; m=m-1)
              `endif
                  pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[102] = upstream_data;
            end
          5:
            begin
              expected_data = pipe_reg[254];
              `ifdef USE_SV
              for (m=254; m>170; m--)
              `else
              for (m=254; m>170; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[170] = upstream_data;
            end
          6:
            begin
              expected_data = pipe_reg[356];
              `ifdef USE_SV
              for (m=356; m>255; m--)
              `else
              for (m=356; m>255; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[255] = upstream_data;
            end
          7:
            begin
              expected_data = pipe_reg[475];
              `ifdef USE_SV
              for (m=475; m>357; m--)
              `else
              for (m=475; m>357; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[357] = upstream_data;
            end
          8:
            begin
              expected_data = pipe_reg[611];
              `ifdef USE_SV
              for (m=611; m>476; m--)
              `else
              for (m=611; m>476; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[476] = upstream_data;
            end
          9:
            begin
              expected_data = pipe_reg[764];
              `ifdef USE_SV
              for (m=764; m>612; m--)
              `else
              for (m=764; m>612; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[612] = upstream_data;
            end
          10:
            begin
              expected_data = pipe_reg[934];
              `ifdef USE_SV
              for (m=934; m>765; m--)
              `else
              for (m=934; m>765; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[765] = upstream_data;
            end
          11:
            begin
              expected_data = pipe_reg[1121];
              `ifdef USE_SV
              for (m=1121; m>935; m--)
              `else
              for (m=1121; m>935; m=m-1)
              `endif
                pipe_reg[m] = pipe_reg[m-1];
              pipe_reg[935] = upstream_data;
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
      cmp_fifo_push = 1'b0;
  end

endmodule
                 
