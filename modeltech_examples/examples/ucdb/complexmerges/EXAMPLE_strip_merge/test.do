onerror resume
transcript on

if { ![info exists ucdb_dir] } {
  set ucdb_dir ../common_ucdbs
}

# Before
vcover merge merge_before.ucdb ${ucdb_dir}/topINITIAL_testAwork.ucdb ${ucdb_dir}/topFINAL_F1_S1_testAwork.ucdb 
vcover report -bydu merge_before.ucdb

#####################################################################
# Modify a copy of a UCDB so that it has the proper merge silhouette.
vsim -viewcov ${ucdb_dir}/topINITIAL_testAwork.ucdb
coverage tag -path /*
coverage tag -path /*/*/S1
coverage edit -path /top/F1/S1 -keeponly
coverage edit -stripdesign 2
coverage tag -path /*
coverage tag -path /*/*/S1
coverage save modified.ucdb

# After
vcover merge merge_after.ucdb modified.ucdb ${ucdb_dir}/topFINAL_F1_S1_testAwork.ucdb 
vcover report -bydu merge_after.ucdb

q -f
