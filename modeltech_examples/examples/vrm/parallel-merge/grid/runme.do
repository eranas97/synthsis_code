vrun generate -rmdb ../generate.rmdb -GNUMTESTS=145
vrun merge -GMODE=sge -GJOBS=4 -GGRIDSLOTS=4 -rmdb $QUESTA_INSTALL/vm_src/parallel-merge/parallel-merge.rmdb -GFILELIST=mylist.txt -GTESTSTATUS=passed
