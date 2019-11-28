
# export PATH:=/u/release/10.4a/questasim/bin:$(PATH)
# export PATH:=/u/release/10.4/questasim/bin:$(PATH)
# export PATH:=/u/release/10.3d/questasim/bin:$(PATH)

export QUESTA_MVC_HOME:=/u/vip/weekly_releases/Questa_VIP_10_4c_1_20151221_uvm
# export QUESTA_MVC_HOME:=/u/vip/library/Questa_VIP_10_4c_uvm
# export QUESTA_MVC_HOME:=/u/vip/library/Questa_VIP_10_3c_uvm

# export VELOCE_XACTOR_HOME:=/medsj/tools/VTL/v3.0
# export VELOCE_XACTOR_HOME:=/home/daerne/builds/Veloce_Transactors_Library_v3.0.2.0

tc_all:
	cd vip_examples/project_benches/qvip_axi4_example/sim; make clean cli; mv transcript /home/daerne/logs/transcript.qvip_axi4
	cd vip_examples/project_benches/vip_axi4_example/sim; make clean cli; mv transcript /home/daerne/logs/transcript.vip_axi4.qvip
	cd vip_examples/project_benches/vip_axi4_example/sim; make clean cli USE_VTL=1; mv transcript /home/daerne/logs/transcript.vip_axi4.vtl

tc_qvip:
	cd vip_examples/project_benches/qvip_axi4_example/sim; make clean cli
	cd vip_examples/project_benches/vip_axi4_example/sim; make clean cli

tc_vtl:
	cd vip_examples/project_benches/vip_axi4_example/sim; make clean cli USE_VTL=1

clean:
	cd vip_examples/project_benches/qvip_axi4_example/sim; make clean
	cd vip_examples/project_benches/vip_axi4_example/sim; make clean
