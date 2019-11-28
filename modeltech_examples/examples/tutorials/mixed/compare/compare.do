#Copyright 1991-2016 Mentor Graphics Corporation
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

vlib work
vmap work work
vlog cache.v memory.v proc.v
vcom util.vhd set.vhd top.vhd
vsim -wlf gold.wlf work.top
add wave *
onbreak {resume}
run -all
quit -sim
