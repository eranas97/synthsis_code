

build:
	-vlib work
	vlog sp_syn_ram.v dp_syn_ram.v ram_tb.v

sim:
	vsim ram_tb 

clean:
	/bin/rm -rf work transcript vsim.wlf data_mem.mem reloc.mem
