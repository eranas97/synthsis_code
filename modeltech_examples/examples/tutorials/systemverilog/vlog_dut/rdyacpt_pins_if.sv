interface rdyacpt_pins_if #(parameter WIDTH = 8) ( );

  bit clk, reset_n;
  bit rdy_di, acpt_di, rdy_do, acpt_do;
  bit [WIDTH-1:0] data_di, data_do;

  modport upstream_mp (
    input  clk,
    input  reset_n,
    input  rdy_di,
    input  data_di,
    output acpt_di
  );

  modport downstream_mp (
    input  clk,
    input  reset_n,
    input  acpt_do,
    output rdy_do,
    output data_do
  );

  modport monitor_mp (
    input  clk,
    input  reset_n,
    input  rdy_di,
    input  data_di,
    input  acpt_di,
    input  acpt_do,
    input  rdy_do,
    input  data_do
  );

  property hs_chk (rdy, acpt, clk);
    @(posedge clk) rdy |-> acpt[->1];
  endproperty

  di_handshake: assert property(hs_chk (rdy_di, acpt_di, clk));
  do_handshake: assert property(hs_chk (rdy_do, acpt_do, clk));

  property data_hold_chk (rdy, acpt, data, clk);
    @(posedge clk) $rose(rdy & !acpt) |=> $past(data,1) === data;
  endproperty

  di_data_hold: assert property(data_hold_chk (rdy_di, acpt_di, data_di, clk));
  do_data_hold: assert property(data_hold_chk (rdy_do, acpt_do, data_do, clk));

endinterface : rdyacpt_pins_if
