vrun generate -rmdb ../generate.rmdb -GNUMTESTS=145
vrun merge -GMODE=rsh -rmdb $QUESTA_INSTALL/vm_src/parallel-merge/parallel-merge.rmdb -GHOSTNAMES="dvtvnc10 dvtvnc11 dvtvnc12 dvtvnc13" -GFILELIST=mylist.txt -GTESTSTATUS=passed
