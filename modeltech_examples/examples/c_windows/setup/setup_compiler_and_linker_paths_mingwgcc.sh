platform=`/usr/bin/basename $b`
no_builtin_compiler=0
`vsim -version | grep "64 vsim" > /dev/null`
if [ $? -eq 0 ]; then
    is64bit=1
	if [ ! -f "$INSTALL_HOME/gcc-4.5.0-mingw64vc12/bin/gcc.exe" ]; then
		no_builtin_compiler=1
		builtin_compiler="gcc-4.5.0-mingw64vc12.zip"
	fi
else
    is64bit=0
	if [ ! -f "$INSTALL_HOME/gcc-4.2.1-mingw32vc12/bin/gcc.exe" ]; then
		no_builtin_compiler=1
		builtin_compiler="gcc-4.2.1-mingw32vc12.zip"
	fi
fi

if [ $no_builtin_compiler -eq 1 ]; then
	echo "Please download and install $builtin_compiler from the Mentor ftp site."
	echo "Using cygwin gcc is not supported."
	exit 0
fi

tcl_ver=`echo "puts stdout \\\$tcl_version" | vish -c`;
tcl_ver=${tcl_ver//[^0-9\.]/};

if [[ $tcl_ver == 8.4* ]] ; then
    tclflags="";
else
    tclflags="";
fi

INSTALL_HOME_WIN_STYLE=`cygpath -w "$INSTALL_HOME"`

if [ $is64bit -eq 1 ] ; then
	CC="$INSTALL_HOME/gcc-4.5.0-mingw64vc12/bin/gcc -g -c -m64 -Wall -std=c99 -I. -I$INSTALL_HOME_WIN_STYLE/include"
	LD="$INSTALL_HOME/gcc-4.5.0-mingw64vc12/bin/gcc -shared -lm -m64 $tclflags -Wl,-Bsymbolic -Wl,-export-all-symbols -o "
	UCDB_LD="$INSTALL_HOME/gcc-4.5.0-mingw64vc12/bin/gcc -lm -m64 $tclflags -o "
else
	CC="$INSTALL_HOME/gcc-4.2.1-mingw32vc12/bin/gcc -g -c -m32 -Wall -ansi -pedantic -I. -I$INSTALL_HOME_WIN_STYLE/include"
	CC="$INSTALL_HOME/gcc-4.2.1-mingw32vc12/bin/gcc -g -c -m32 -Wall -ansi -pedantic -I. -I$INSTALL_HOME_WIN_STYLE/include"
	LD="$INSTALL_HOME/gcc-4.2.1-mingw32vc12/bin/gcc -shared -lm -m32 $tclflags -Wl,-Bsymbolic -Wl,-export-dynamic -o"
	UCDB_LD="$INSTALL_HOME/gcc-4.2.1-mingw32vc12/bin/gcc -lm -m32 $tclflags -o"
fi
MTIPLILIB=" -L$INSTALL_HOME_WIN_STYLE/$platform -lmtipli"
UCDBLIB="-L$INSTALL_HOME_WIN_STYLE/$platform -lucdb"
