onerror resume
transcript on

if { ![info exists ucdb_dir] } {
  set ucdb_dir ../common_ucdbs
}

rm -rf ${ucdb_dir}/top*
rm -rf ${ucdb_dir}/bench*

#
#	Simulate:
#
rm -rf work
rm -rf lib
vlib work
vlog -work work -cover bcestf testB.sv
vsim -lib work -c -coverage work.bench
set test testBwork
set top bench
do createUCDB.do

rm -rf work
rm -rf lib
vlib work
vlog -work work -cover bcestf testA.sv
vsim -lib work -c -coverage work.top
set test testAwork
set top top
do createUCDB.do

rm -rf work
rm -rf lib
vlib lib
vlog -work lib -cover bcestf testA.sv
vsim -lib lib -c -coverage lib.top
set test testAlib
set top top
do createUCDB.do

q -f
