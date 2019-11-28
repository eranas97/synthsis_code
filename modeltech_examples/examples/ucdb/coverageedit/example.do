transcript on
onerror { resume }
onbreak { resume }
run -all

coverage report -byinst
coverage save original.ucdb

# === Delete everything but /top/dut* (ie. keep DUT) ===
coverage open original.ucdb
coverage edit -keeponly -path /top/dut*
coverage report -byinst
coverage save dut.ucdb

# === Delete nothing but /top/dut* (ie. keep TB) ===
coverage open original.ucdb
coverage edit -delete -path /top/dut*
coverage report -byinst
coverage save tb.ucdb

quit
