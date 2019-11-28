#
# Makefile for TestTracking example
#
# Type:  make compile               Compile design
#        make run[{10,20,60}]       Run simulations
#       [make results.rank]         Rank tests
#        make {excel|word|docbook}  Import testplan and merge
#        make report                Generate HTML report
#        make triage                Generate triage report
#
# See README for more details.
#

all:
					@echo "Usage: make clean (optional)"
					@echo "       make compile"
					@echo "       make {run|run10|run20|run60}"
					@echo "       make {excel|word|docbook}"
					@echo "       make report (optional)"
					@echo "       make triage (optional)"
					@echo "See README for more information"

gui:
					vsim -cvgperinstance -cvgmergeinstances -msgmode both concat_tester

guidemo:			clean gui

excel:				clean_tp concat_excel.ucdb results.dump
					cp results.dump concat_excel.dump

word:				clean_tp concat_word.ucdb results.dump
					cp results.dump concat_word.dump

docbook:			clean_tp concat_dbook.ucdb results.dump
					cp results.dump concat_dbook.dump

concat_excel.ucdb:	xml/concat_excel.xml
					xml2ucdb -format Excel -dofilename concat_excel.do $< $@
					echo $@ > tplan.list

concat_word.ucdb:	xml/concat_word.xml
					xml2ucdb -format Word -dofilename concat_word.do $< $@
					echo $@ > tplan.list

concat_dbook.ucdb:	xml/concat_dbook.xml
					xml2ucdb -format DocBook -dofilename concat_dbook.do $< $@
					echo $@ > tplan.list

results.rank:
					vcover ranktest -rankfile $@ `cat sim.list`

results.ucdb:		clean_res
					rm -rf $@
					vcover merge $@ `cat tplan.list` `cat sim.list`

%.dump:				%.ucdb
					vsim -c -viewcov $< -do "coverage analyze -plan / -r -file $@; quit -f"

triage:				results.ucdb
					vsim -c -do "triage dbfile -clear -teststatus FEWP -severity FEWN results.ucdb; quit -f"
					vsim -c -do "triage report -file triage.report; quit -f"

report:
					vcover report -html -htmldir covreport results.ucdb

compile:
					vsim -c -do "source scripts/compile.do; quit -f"

run:
					vsim -cvgperinstance -cvgmergeinstances -c -do "source scripts/rundirected.do; quit -f"
					ls -1 *.ucdb | grep -v concat | grep -v results | sort > sim.list

run10:
					vsim -cvgperinstance -cvgmergeinstances -c -do "source scripts/rundirected.do; quit -f"
					vsim -cvgperinstance -cvgmergeinstances -c -do "source scripts/runrandom10.do; quit -f"
					ls -1 *.ucdb | grep -v concat | grep -v results | sort > sim.list

run20:
					vsim -cvgperinstance -cvgmergeinstances -c -do "source scripts/rundirected.do; quit -f"
					vsim -cvgperinstance -cvgmergeinstances -c -do "source scripts/runrandom20.do; quit -f"
					ls -1 *.ucdb | grep -v concat | grep -v results | sort > sim.list

run60:
					vsim -cvgperinstance -cvgmergeinstances -c -do "source scripts/rundirected.do; quit -f"
					vsim -cvgperinstance -cvgmergeinstances -c -do "source scripts/runrandom60.do; quit -f"
					ls -1 *.ucdb | grep -v concat | grep -v results | sort > sim.list

# clean testplan files
clean_tp:
					rm -rf concat_excel.ucdb
					rm -rf concat_word.ucdb
					rm -rf concat_dbook.ucdb
					rm -rf tplan.list

# clean merge/rank results
clean_res:			clean_tp
					rm -rf results.rank results.contrib results.noncontrib
					rm -rf results.ucdb results.dump transcript

# clean everything
clean:				clean_res
					rm -rf work *.log *.ucdb *.do *.dump *.wlf covreport sim.list triage*.report questasim.tdb
