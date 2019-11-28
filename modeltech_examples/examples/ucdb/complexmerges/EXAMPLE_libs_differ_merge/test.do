onerror resume
transcript on

if { ![info exists ucdb_dir] } {
  set ucdb_dir ../common_ucdbs
}

# Before
vcover merge merge_before.ucdb ${ucdb_dir}/topINITIAL_testAlib.ucdb ${ucdb_dir}/topFINAL_testAwork.ucdb 
vcover report -bydu merge_before.ucdb

#####################################################################
# Modify a copy of a UCDB so that it has the proper merge silhouette.
vsim -viewcov ${ucdb_dir}/topINITIAL_testAlib.ucdb
coverage tag -du *
coverage edit -rename -lib lib work
coverage tag -du *
coverage save modified.ucdb

# After
vcover merge merge_after.ucdb  modified.ucdb ${ucdb_dir}/topFINAL_testAwork.ucdb
vcover report -bydu merge_after.ucdb

q -f
