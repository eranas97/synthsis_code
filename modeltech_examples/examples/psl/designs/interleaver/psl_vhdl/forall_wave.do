add wave -noupdate -format Logic /interleaver_tester/reset
add wave -noupdate -format Logic /interleaver_tester/clk
add wave -noupdate -format Literal -radix unsigned /interleaver_tester/upstream_data
add wave -noupdate -format Logic /interleaver_tester/upstream_rdy
add wave -noupdate -format Logic /interleaver_tester/upstream_acpt
add wave -noupdate -format Literal -radix unsigned /interleaver_tester/downstream_data
add wave -noupdate -format Logic /interleaver_tester/downstream_rdy
add wave -noupdate -format Logic /interleaver_tester/downstream_acpt
add wave -noupdate -format Literal -radix unsigned /interleaver_tester/expected_data
add wave -noupdate -format Literal -radix unsigned /interleaver_tester/cmp_fifo_data
add wave -noupdate -format Logic /interleaver_tester/cmp_fifo_push
add wave -noupdate -format Logic /interleaver_tester/cmp_fifo_pop
add wave -noupdate -format Literal -radix unsigned /interleaver_tester/interleaver1/fifo/waddr
add wave -noupdate -format Literal -radix unsigned /interleaver_tester/pipe_reg
add wave -noupdate -format Literal -radix unsigned /interleaver_tester/interleaver1/do_reg
add wave -noupdate -format Literal /interleaver_tester/interleaver1/int_state
add wave -noupdate -format Literal /interleaver_tester/interleaver1/fifo/push
add wave -noupdate -format Literal -radix unsigned /interleaver_tester/up_hs_less10_cnt
add wave -noupdate -divider Assertions
add wave -noupdate -format Literal /interleaver_tester/\\ended(up_hs_less10_hit)\\
add wave -noupdate -format Literal /interleaver_tester/interleaver1/assert__sync_bypass_check
add wave -noupdate -format Literal /interleaver_tester/interleaver1/assert__pkt_start_check
add wave -noupdate -format Literal /interleaver_tester/interleaver1/assert__pkt_length_check
add wave -noupdate -format Literal /interleaver_tester/interleaver1/fifo/assert__ram_write_check
add wave -noupdate -format Literal /interleaver_tester/interleaver1/c_interleave_sm
add wave -noupdate -format Literal /interleaver_tester/c_no_dwn_hs_more_10
add wave -noupdate -format Literal /interleaver_tester/c_no_dwn_hs_less_10
add wave -noupdate -format Literal /interleaver_tester/c_no_up_hs_more_10
add wave -noupdate -format Literal /interleaver_tester/c_no_up_hs_less_10
