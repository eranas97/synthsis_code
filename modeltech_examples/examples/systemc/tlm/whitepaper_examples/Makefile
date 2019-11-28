# ###########################################################################
# Makefile for running TLM examples with ModelSim SystemC and/or OSCI SystemC.
# ###########################################################################
#
# --------------------------------------------------------------------
# 1. Build and run TLM Examples using ModelSim SystemC:
#
#   make mti
#
#     # This causes each example to be run in turn, for example:
#       foreach EXAMPLE {
#          cd EXAMPLE                        cd example_5_1
#          vsim -c -do run.do                vsim -c -do run.do
#       }
#
#     # You can also run everything completely by hand (see the contents of run.do):
#         cd example_5_2
#         vlib work
#
#       # Compile
#         sccom -I../../utils -I../basic_protocol -I../user -g main.cc
#         sccom -I../../utils -I../basic_protocol -I../user -g ../user/master.cc  
#         sccom -I../../utils -I../basic_protocol -I../user -g ../user/mem_slave.cc  
#         sccom -I../../utils -I../basic_protocol -I../user -g ../user/switch_master.cc 
#         sccom -link
#
#       # Simulate
#         vsim -c top -do "run 100 ns; quit -f"
#
# --------------------------------------------------------------------
# 2. Build and run TLM Examples using OSCI SystemC:
#
#   # Setup SYSTEMC_HOME to point to the SystemC location where 'include' lives.
#   # Setup TLM_HOME to point to the place where the TLM Kit is unpacked.
#
#   # For example:
#      setenv TLM_HOME     /u/redelman/Transactions/examples/tlm_17nov04/tlm
#      setenv SYSTEMC_HOME /u/redelman/SystemC/systemc-2.1beta10
#
#	make osci
#


EXAMPLES = example_3_2 example_3_3 example_3_4 example_3_5 \
			example_4_1 example_4_2 example_4_3 example_4_4 \
			example_5_1 example_5_2

all: clean osci clean mti

mti:
	@for x in $(EXAMPLES);do \
		echo "" ; \
		echo "Running MTI $$x"; \
		cd $$x; \
		vsim -c -do run.do; \
		cp -p transcript results; \
		mv transcript mti.transcript; \
		cd ..; \
	done

osci:
	@for x in $(EXAMPLES);do \
		echo "" ; \
		echo "Running OSCI $$x"; \
		cd $$x; \
		make -f osci_make; ./TLMrun > osci.transcript; \
		cat osci.transcript; \
		cd ..; \
	done

# Chicken and the Egg.
#  In the TLM Kit released version of the makefile, the target
#  "clean_osci" invokes sub-makes which depended on "Make.dep", which can't be
#  created unless SYSTEMC_HOME, etc are correct; which means
#  you can't CLEAN UP UNLESS YOUR ENVIRONMENT IS SET-UP.
#
#  Seting up your environment can be tough - especially if you really
#  just want to run MTI stuff - which DOES NOT require much (any?) environment
#  setup. Seems like a tough requirement to have to setup the ENV before cleaning. 
#  SO, we pulled the "clean" functionality 'rm ...' from osci_make DIRECTLY into the
#  line below. So now we clean up by ONLY doing:
#		make clean
#
clean_osci: 
	rm -f example*/*.o example*/*.dep example*/TLMrun* example*/*~ user/*.o

clean_mti:
	rm -f */transcript
	rm -rf */work
	rm -f */vsim.wlf

clean: clean_osci clean_mti

realclean: clean
	rm -f */osci.transcript
	rm -f */mti.transcript
	rm -f */workingExclude.cov
	rm -f example_3_2/core.*

