onerror {resume}
onbreak {resume}

add wave  /top/fpu_dut/*
add wave  /top/fpu_pins/check_add_delay
add wave /top/fpu_pins/check_sub_delay
add wave /top/fpu_pins/check_mult_delay
add wave  /top/fpu_pins/check_div_delay
add wave /top/fpu_pins/check_sqrt_delay
log -r /*
