if { ![info exists ucdb_dir] } {
  set ucdb_dir ../common_ucdbs
}
run 0
coverage save ${ucdb_dir}/${top}INITIAL_${test}.ucdb
run 10000
coverage save ${ucdb_dir}/${top}FINAL_${test}.ucdb
coverage save -instance /${top}/F1/S1 ${ucdb_dir}/${top}FINAL_F1_S1_${test}.ucdb
