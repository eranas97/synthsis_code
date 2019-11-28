onerror { resume }
onbreak { resume }
transcript on

# This converts the testplan.csv file (output from a spreadsheet) to a UCDB
# incorporating the test plan:
exec csv2ucdb testplan.csv

# Can't rely on shell ordering of simple?.ucdb:
# This example is adapted from a Questa regression, it turns out simple?.ucdb
# globs in a different order on different platforms; this has no functional
# effect except that queries like -coverage nonzero give test name results in a
# different order.
# If you don't care, just do:
#   vcover merge simple.ucdb testplan.ucdb simple?.ucdb
#
vcover merge simple.ucdb testplan.ucdb simple1.ucdb simple2.ucdb simple3.ucdb simple4.ucdb -testassociated
vsim -viewcov simple.ucdb

# This is the basic query upon which the Verification Management Tracker GUI is
# based:
coverage analyze -r -plan /

# Tests of -testextract:
coverage analyze -r -plan / -test simple1_1
coverage analyze -r -plan / -test simple2_2
coverage analyze -r -plan / -test simple1_1 simple2_2

# Tests of -coverage:
coverage analyze -plan /testplan/*/* -coverage most
coverage analyze -plan /testplan/*/* -coverage least
coverage analyze -plan /testplan/*/* -coverage zero
coverage analyze -plan /testplan/*/* -coverage nonzero

# Most for covergroups:
coverage analyze -path /top/*/* -cvg -coverage most
coverage analyze -path /top/*/* -cvg -coverage least
coverage analyze -path /top/*/* -cvg -coverage zero
coverage analyze -path /top/*/* -cvg -coverage nonzero

# Tests of -summary:
coverage analyze -r -plan / -summary
coverage analyze -path /top -summary hier
coverage analyze -path /top -summary local
# Note that -summary with a path implies "-select instance", so that the
# summary report gives summary for design instances:
coverage analyze -path /top -r -summary

# Here are some tests of coverage unlinked, for cases where the test plan does
# NOT include all coverage, or all coverage is not included in the test plan.
# To demonstrate this, however, requires breaking one of the links in our
# currently well-constructed test plan:
#
coverage tags -delete -match cvg_bits_vs_clock -tagname "1.1"
# This should find /top/child1/cvg_bits_vs_clock:
coverage unlinked -r -path / -cvg
coverage unlinked -r -path / -cvg -allunlinked

coverage tags -delete -plan /testplan/*Top/*Arithmetic -tagname "1.2"
# This should find /testplan/*Top/*Arithmetic:
coverage unlinked -r -plan /

# reload dataset and start over
dataset close simple
vsim -viewcov simple.ucdb

# Tests of select filter
coverage analyze -plan / -r -select weight -eq 2
coverage analyze -plan / -r -select weight -eq 1
coverage analyze -plan / -r -select weight -eq 1 -test simple1_1 simple2_2
coverage analyze -plan / -r -select weight -eq 1 -select tag -eq 1.2
coverage analyze -plan / -r -select coverage -lt 50 
coverage analyze -plan / -r -select coverage -lt 50 -aggregate preselect

coverage analyze -path / -r -cvg -select weight -eq 0
coverage analyze -path / -r -cvg -select weight -gt 0
