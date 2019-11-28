set files [glob -nocomplain *.o *.wlf core* *.exp *.lib *.obj *.dll *.h *.vstf]
foreach file $files {
	file delete -force $file
}
file delete -force results.txt
file delete -force work
quit -f
