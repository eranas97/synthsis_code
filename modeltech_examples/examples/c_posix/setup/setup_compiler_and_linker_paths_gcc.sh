`vsim -version | grep "64 vsim" > /dev/null`
if [ $? -eq 0 ]; then
    is64bit=1
else
    is64bit=0
fi

tcl_ver=`echo "puts stdout \\\$tcl_version" | vish -c`;
tcl_ver=${tcl_ver//[^0-9\.]/};

if [[ $tcl_ver == 8.4* ]] ; then
    tclflags="";
else
    tclflags="-lpthread";
fi

os=`uname`
machine=`uname -m`

case $os in 
Linux)
	if [ $is64bit -eq 1 ] ; then
		platform=linux_x86_64
	else
		platform=linux
	fi
	;;
SunOS)
	if [ $is64bit -eq 1 ] ; then
		if [ "$machine" = "i86pc" ]; then
			platform=sunos5x86_64
		else
			platform=sunos5v9
		fi
	else
		if [ "$machine" = "i86pc" ]; then
			platform=sunos5x86
		else
			platform=sunos5
		fi
	fi 
	;;
*)
	echo "Script not configured for $os, see User's manual."
	exit 0
	;;
esac

if [ $is64bit -eq 1 ] ; then
	if [ "$os" = "SunOS" ]; then
		CC="gcc -g -c -m64 -Wall -fPIC -I. -I$INSTALL_HOME/include"
		LD="/usr/ccs/bin/ld -G -Bsymbolic $tclflags -o"
		if [ "$platform" = "sunos5v9" ]; then
			CC="cc -xarch=v9 -xcode=pic32 -c -I$INSTALL_HOME/include"
		fi
	else
		CC="gcc -g -c -m64 -Wall -ansi -pedantic -fPIC -I. -I$INSTALL_HOME/include"
		LD="gcc -shared -lm -m64 $tclflags -Wl,-Bsymbolic -Wl,-export-dynamic -o "
	fi
	UCDB_LD="gcc -ldl -lm -m64 $tclflags -o "
else
	if [ "$os" = "SunOS" ]; then
		CC="gcc -g -c -m32 -Wall -I. -I$INSTALL_HOME/include"
		LD="/usr/ccs/bin/ld -G -Bsymbolic $tclflags -o"
	else
		CC="gcc -g -c -m32 -Wall -ansi -pedantic -I. -I$INSTALL_HOME/include"
		LD="gcc -shared -lm -m32 $tclflags -Wl,-Bsymbolic -Wl,-export-dynamic -o"
	fi
	UCDB_LD="gcc -ldl -lm -m32 $tclflags -o"

fi
UCDBLIB="$INSTALL_HOME/$platform/libucdb.a"
