onerror resume
transcript on

if { ![info exists ucdb_dir] } {
  set ucdb_dir ../common_ucdbs
}

# Before
vcover merge merge_before.ucdb ${ucdb_dir}/topINITIAL_testAwork.ucdb ${ucdb_dir}/benchFINAL_testBwork.ucdb 
vcover report -bydu merge_before.ucdb

#####################################################################
# Modify a copy of a UCDB so that it has the proper merge silhouette.
vsim -viewcov ${ucdb_dir}/benchFINAL_testBwork.ucdb
coverage tag -path /*/THIS_NAME_DOES_NOT_MATCH
coverage tag -path /*/F2
coverage edit -rename -path /bench/THIS_NAME_DOES_NOT_MATCH F2
coverage edit -rename -path /bench top
coverage tag -path /*/THIS_NAME_DOES_NOT_MATCH
coverage tag -path /*/F2
coverage save modified.ucdb

# After
vcover merge merge_after.ucdb ${ucdb_dir}/topINITIAL_testAwork.ucdb modified.ucdb
vcover report -bydu merge_after.ucdb

q -f
