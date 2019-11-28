onbreak resume

set TestName "IntialTest ModeTwoTest DataTest FifoTest \
              CPURegisterTest VariableTest TxDataTest SyncTest"

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

for {set test 0} {$test < 7} {incr test} {

  set testname [lindex $TestName $test]

  vsim -cvgperinstance -cvgmergeinstances \
       -cover -vopt -assertdebug work.concat_tester -GTEST=$test -GSIM_TIME=1 \
       -msgmode both -wlf $testname.wlf -l $testname.log

  add log /*
  assertion fail -log off -r /

  run -all

  coverage attr -name TESTNAME \
                -value $testname   
  coverage attr -name  SCRIPT \
                -value $script
  coverage attr -name  COMPILE \
                -value compile.do
  coverage attr -name  INITIAL \
                -value modelsim.tcl
  coverage attr -name  WLFNAME \
                -value $testname.wlf
  coverage attr -name  TRANSCRIPTNAME \
                -value $testname.log
  coverage attr -name  WARNINGS \
                -value [GrepAndReturnCounts Warning $testname.log]
  coverage attr -name  ERRORS \
                -value [GrepAndReturnCounts Error $testname.log]
  coverage attr -name  REGREADS \
                -value [GrepAndReturnCounts {Read Register} $testname.log]

  coverage save $testname.ucdb

  quit -sim
}
