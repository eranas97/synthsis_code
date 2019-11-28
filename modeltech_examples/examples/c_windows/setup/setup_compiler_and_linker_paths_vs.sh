platform=`/usr/bin/basename $b`
`vsim -version | grep "64 vsim" > /dev/null`
if [ $? -eq 0 ]; then
    is64bit=1

else
    is64bit=0
fi

INSTALL_HOME_WIN_STYLE=`cygpath -w "$INSTALL_HOME"`

TOOLPATH=`regtool -q get /HKLM/SOFTWARE/Microsoft/VisualStudio/12.0/Setup/VC/ProductDir`
if [ $? -ne 0 ]; then
	VCEDITION="VCExpress"
else 
	VCEDITION="VisualStudio"
fi

# Reset VCEDITION to VisualStudio for 64-bit Windows. 
# VCExpress does not have 64-bit executables.
if [ $is64bit -eq 1 ]; then
	VCEDITION="VisualStudio"
fi

TOOLPATH=`regtool get /HKLM/SOFTWARE/Microsoft/$VCEDITION/12.0/Setup/VC/ProductDir`
TOOLPATH=`cygpath -ms "$TOOLPATH"`
TOOLPATHu=`cygpath -u "$TOOLPATH"`
if [ $is64bit -eq 1 ]; then
	cl_path="bin/amd64"
else
	cl_path="bin"
fi

if [ ! -f "$TOOLPATH/$cl_path/cl" ] ; then
	echo "ERROR: Couldn't find cl.exe on your machine. Please install Visual Studio 12.0."
	exit 0
else
	PATH="${TOOLPATHu}:${TOOLPATHu}${cl_path}:$PATH"
fi

if [ $is64bit -eq 0 ]; then
	MSPDB120u=`cygpath -u "$TOOLPATHu"`
	MSPDB120=`cygpath -ms "$TOOLPATH"`
	if [ ! -f "$MSPDB120/bin/mspdb120.dll" ] ; then
		echo "ERROR: Couldn't find $MSPDB120/mspdb120.dll. Please install the required mspdb120.dll."
		exit 0
	else
		PATH="$MSPDB120u/bin:$PATH"
	fi
fi

SDKPATH=`regtool get "/HKLM/SOFTWARE/Microsoft/Microsoft SDKs/Windows/v8.1/InstallationFolder"`
SDKPATH=`cygpath -ms "$SDKPATH"`
SDKPATHu=`cygpath -u "$SDKPATH"`
if [ $is64bit -eq 1 ]; then
	mt_path="bin/x64"
else 
	mt_path="bin/x86"
fi

if [ ! -f "$SDKPATH/$mt_path/mt.exe" ]; then
	echo "ERROR: Couldn't find $SDKPATH/$mt_path/mt.exe. Please install the required SDK."
	exit 0
else
	PATH="${SDKPATHu}${mt_path}:$PATH"
fi


export INCLUDE="${TOOLPATH}include;${SDKPATH}include"
if [ $is64bit -eq 1 ]; then
	export LIB="${TOOLPATH}lib/amd64;${SDKPATH}lib/winv6.3/um/x64"
else
	export LIB="${TOOLPATH}lib;${SDKPATH}lib/winv6.3/um/x86"
fi

CC="cl -c -Ox -Oy -I. -I$INSTALL_HOME_WIN_STYLE\\include"
LD="link /DLL $INSTALL_HOME_WIN_STYLE\\$platform\\mtipli.lib"
UCDB_LD="link /NODEFAULTLIB:libcmt.lib"
UCDBLIB="-DEFAULTLIB:$INSTALL_HOME_WIN_STYLE\\$platform\\ucdb.lib"
UCDBLIB_STATIC="$INSTALL_HOME_WIN_STYLE\\$platform\\libucdb.lib"
