quietly set platform [file tail $env(MODEL_TECH)]
# Check if 64-bit executables are being run.
if {[string match "*64 vsim*" [vsim -version]]} {
	quietly set is64bit 1
	quietly set gcc_path "$INSTALL_HOME/gcc-4.5.0-mingw64vc12/bin"
	quietly set mingw_gcc_exists [file exists  "$INSTALL_HOME/gcc-4.5.0-mingw64vc12/bin/gcc.exe"]
	quietly set builtin_compiler "gcc-4.5.0-mingw64vc12.zip"
} else {
	quietly set is64bit 0
	quietly set gcc_path "$INSTALL_HOME/gcc-4.2.1-mingw32vc12/bin"
	quietly set mingw_gcc_exists [file exists  "$INSTALL_HOME/gcc-4.2.1-mingw32vc12/bin/gcc.exe"]
	quietly set builtin_compiler "gcc-4.2.1-mingw32vc12.zip"
}

#check if we are using tcl8.5
if { [string match 8.4* $tcl_patchLevel] } {
	set tclflags ""
} else {
	set tclflags ""
}

if {$mingw_gcc_exists != 1} {
	echo "Please download and install $builtin_compiler from the Mentor ftp site."
	echo "Using cygwin gcc is not supported."
	quit -f
}

quietly set env(PATH) "$gcc_path;$::env(PATH)"
# quietly setup - quietly set path to the C compiler and linker.
if {$is64bit == 1 } {
	quietly set CC "gcc -g -c -m64 -Wall -I. -I$INSTALL_HOME/include "
	quietly set LD "gcc -shared -lm -m64 $tclflags -Wl,-Bsymbolic -Wl,-export-all-symbols -o "
	quietly set UCDB_LD "gcc -lm -m64 $tclflags -o "
} else {
	quietly set CC "gcc -g -c -m32 -Wall -ansi -pedantic -I. -I$INSTALL_HOME/include "
	quietly set LD "gcc -shared -lm -m32 $tclflags -Wl,-Bsymbolic -Wl,-export-dynamic -o "
	quietly set UCDB_LD "gcc -lm -m32 $tclflags -o "
}
quietly set MTIPLILIB " -L$INSTALL_HOME/$platform -lmtipli"
quietly set UCDBLIB " -L$INSTALL_HOME/$platform -lucdb"
quietly set ext "dll"
