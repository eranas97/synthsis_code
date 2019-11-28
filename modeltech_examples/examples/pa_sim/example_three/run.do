if [file exists work] {
    vdel -all
}
onbreak {resume}
vlib work
vlog -sv alu_tester.sv top_rtl.v register.v iopad.v alu.v mux.v
vopt alu_tester -o tbout +acc -pa_upf rtl_top.upf -pa_genrpt -pa_enable=libertypamodel -pa_libertyfiles=pa.lib -pa_enable=highlight+debug
vsim tbout -pa -pa_highlight
add wave -r * 
run -all
if {[batch_mode]} {
    quit -f
}
