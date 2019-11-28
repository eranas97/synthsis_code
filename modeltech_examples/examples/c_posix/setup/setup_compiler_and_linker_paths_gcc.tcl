
# Check if 64-bit executables are being run.
if {[string match "*64 vsim*" [vsim -version]]} {
	quietly set is64bit 1
	if {$tcl_platform(os) eq "Linux"} {
		quietly set platform "linux_x86_64"
	} elseif {$tcl_platform(os) eq "SunOS"} {
		if {$tcl_platform(machine) eq "i86pc"} {
			quietly set platform "sunos5x86_64"
		} else {
			quietly set platform "sunos5v9"
		}
	}
} else {
	quietly set is64bit 0
	if {$tcl_platform(os) eq "Linux"} {
		quietly set platform "linux"
	} elseif {$tcl_platform(os) eq "SunOS"} {
		if {$tcl_platform(machine) eq "i86pc"} {
			quietly set platform "sunos5x86"
		} else {
			quietly set platform "sunos5"
		}
	}
}

#check if we are using tcl8.5
if { [string match 8.4* $tcl_patchLevel] } {
	set tclflags ""
} else {
	set tclflags "-lpthread"
}

# quietly set path to the C compiler and linker.
if {$is64bit == 1 } {
	if {$tcl_platform(os) eq "SunOS"} {
		quietly set CC "gcc -g -c -m64 -Wall -fPIC -I. -I$INSTALL_HOME/include "
		quietly set LD "/usr/ccs/bin/ld -G -Bsymbolic $tclflags -o"
		if {$platform eq "sunos5v9"} {
			quietly set CC "cc -xarch=v9 -xcode=pic32 $tclflags -c -I$INSTALL_HOME/include"
		}
	} else {
		quietly set CC "gcc -g -c -m64 -Wall -ansi -pedantic -fPIC -I. -I$INSTALL_HOME/include "
		quietly set LD "gcc -shared -lm -m64 $tclflags -Wl,-Bsymbolic -Wl,-export-dynamic -o "
	}
	quietly set UCDB_LD "gcc -ldl -lm -m64 $tclflags -o "
} else {
	if {$tcl_platform(os) eq "SunOS"} {
		quietly set CC "gcc -g -c -m32 -Wall -I. -I$INSTALL_HOME/include "
		quietly set LD "/usr/ccs/bin/ld -G -Bsymbolic $tclflags -o"
	} else {
		quietly set CC "gcc -g -c -m32 -Wall -ansi -pedantic -I. -I$INSTALL_HOME/include "
		quietly set LD "gcc -shared -lm -m32 $tclflags -Wl,-Bsymbolic -Wl,-export-dynamic -o "
	}
	quietly set UCDB_LD "gcc -ldl -lm -m32 $tclflags -o"
}

quietly set UCDBLIB "$INSTALL_HOME/$platform/libucdb.a"
quietly set MTIPLILIB " "
quietly set ext "so"
