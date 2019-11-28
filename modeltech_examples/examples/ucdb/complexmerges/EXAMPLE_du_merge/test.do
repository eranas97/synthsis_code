onerror resume
transcript on

if { ![info exists ucdb_dir] } {
  set ucdb_dir ../common_ucdbs
}

# BAD
vcover merge                  merge_bad.ucdb ${ucdb_dir}/topINITIAL_testAwork.ucdb ${ucdb_dir}/topFINAL_F1_S1_testAwork.ucdb 
vcover report -bydu merge_bad.ucdb

# GOOD
vcover merge -du work.second merge_good.ucdb ${ucdb_dir}/topINITIAL_testAwork.ucdb ${ucdb_dir}/topFINAL_F1_S1_testAwork.ucdb
vcover report -bydu merge_good.ucdb

q -f
