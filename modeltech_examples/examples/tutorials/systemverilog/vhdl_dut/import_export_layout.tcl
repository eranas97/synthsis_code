proc export_layout {outfile} {
   set outf [open $outfile w]
   puts $outf [.main_pane serialize]
   close $outf
   }

proc import_layout {infile} {
   set inf [open $infile r]
   .main_pane unserialize [gets $inf]
   close $inf
}
