if [file exists work] {
    vdel -all
}
onbreak {resume}
vlib work
vlog -sv alu_tester.sv top_rtl.v register.v iopad.v alu.v mux.v
vopt alu_tester -o tbout +acc -pa_upf rtl_top.upf -pa_genrpt -pa_checks -pa_coverage=checks -pa_enable=highlight+debug
vsim tbout -pa -coverage -pa_highlight
add wave -r * 
run -all
coverage report -pa -detail
if {[batch_mode]} {
    quit -f
}
