onbreak resume

set tests 60

proc GrepAndReturnCounts {searchString searchFile} {
  if {![catch {exec grep $searchString $searchFile } error]} {
    return [expr [regexp -all {\n} $error] + 1]
  } else {
    return 0
  }
}

#
#	Set $script to script contents if -do used with vsim:
#
set do_arg [lsearch $argv -do]
if {$do_arg == -1} {
	set script none
} else {
	set script [lindex $argv [expr $do_arg + 1]]
}

for {set test 7} {$test < $tests} {incr test} {

  set Unique [clock seconds]
  set testname  [format "Random%d_" $test]
  set seed1 [expr int(rand() * 100)]
  set seed2 [expr int(rand() * 100)]

  # Change the "20" to something larger for longer simulations

  set runtime [expr int(rand() * 20)]

  vsim -cover -vopt -cvgperinstance -cvgmergeinstances -assertdebug work.concat_tester -sv_seed $seed1 \
       -GTEST=$test -GSIM_TIME=$runtime -GREGseed=$seed1 -GVARSeed=$seed2 \
       -wlf $testname$Unique.wlf -l $testname$Unique.log

  add log /*
  assertion fail -log off -r /
  run -all

  coverage attr -name  TESTNAME \
                -value [string range $testname 0 end-1]
  coverage attr -name  SCRIPT \
                -value $script
  coverage attr -name  COMPILE \
                -value compile.do
  coverage attr -name  INITIAL \
                -value modelsim.tcl
  coverage attr -name  WLFNAME \
                -value $testname$Unique.wlf
  coverage attr -name  TRANSCRIPTNAME \
                -value $testname$Unique.log
  coverage attr -name  WARNINGS \
                -value [GrepAndReturnCounts Warning $testname$Unique.log]
  coverage attr -name  ERRORS \
                -value [GrepAndReturnCounts Error $testname$Unique.log]
  coverage attr -name  REGREADS \
                -value [GrepAndReturnCounts {Read Register} $testname$Unique.log]

  coverage save $testname$Unique.ucdb

  quit -sim
}
