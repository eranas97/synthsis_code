vrun generate -rmdb ../generate.rmdb -GNUMTESTS=145
vrun merge -GMODE=local -rmdb $QUESTA_INSTALL/vm_src/parallel-merge/parallel-merge.rmdb -GFILELIST=mylist.txt -GTESTSTATUS=passed -j 1
vrun merge -GMODE=local -rmdb $QUESTA_INSTALL/vm_src/parallel-merge/parallel-merge.rmdb -GFILELIST=mylist.txt -GTESTSTATUS=passed -j 2
vrun merge -GMODE=local -rmdb $QUESTA_INSTALL/vm_src/parallel-merge/parallel-merge.rmdb -GFILELIST=mylist.txt -GTESTSTATUS=passed -ask
