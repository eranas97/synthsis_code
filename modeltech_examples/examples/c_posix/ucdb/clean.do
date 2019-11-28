set files [glob -nocomplain *.o *.wlf core* *.exp *.lib *.obj *.dll *.h *.vstf *.dump *.ucdb]
foreach file $files {
	file delete -force $file
}
file delete -force ucdbdump
file delete -force work
quit -f
