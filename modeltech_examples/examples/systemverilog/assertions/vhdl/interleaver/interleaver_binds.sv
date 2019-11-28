module interleaver_binds #(parameter RUNFC = 0) ;
//module interleaver_binds ;

//bind interleaver_tester sva_top_props #(RUNFC) sva_top_props_bind (
bind interleaver_tester sva_top_props sva_top_props_bind (
   .clk(clk),
   .upstream_rdy(upstream_rdy),
   .upstream_acpt(upstream_acpt),
   .upstream_data(upstream_data), 
   .downstream_rdy(downstream_rdy),
   .downstream_acpt(downstream_acpt),
   .downstream_data(downstream_data),
   .cmp_fifo_data(cmp_fifo_data)
   );

bind interleaver_m0 interleaver_props interleaver_props_bind (
   .clk(clk),
   .in_hs(in_hs),
   .out_hs(out_hs),
   .input_down_data(input_down_data),
   .do_reg(do_reg),
   .int_state_vec(int_state) 
   );

bind fifo_shift_ram fifo_shift_ram_props fifo_shift_ram_props_bind (
   .clk(clk),
   .ram_re(ram_re),
   .ram_we(ram_we),
   .push(push),
   .addra(addra),
   .addrb(addrb),
   .waddr1(waddr1),
   .waddr2(waddr2), 
   .waddr3(waddr3), 
   .waddr4(waddr4), 
   .waddr5(waddr5), 
   .waddr6(waddr6), 
   .waddr7(waddr7), 
   .waddr8(waddr8), 
   .waddr9(waddr9), 
   .waddr10(waddr10), 
   .waddr11(waddr11),
   .raddr1(raddr1),
   .raddr2(raddr2), 
   .raddr3(raddr3), 
   .raddr4(raddr4), 
   .raddr5(raddr5), 
   .raddr6(raddr6), 
   .raddr7(raddr7), 
   .raddr8(raddr8), 
   .raddr9(raddr9), 
   .raddr10(raddr10), 
   .raddr11(raddr11)
   );

endmodule
