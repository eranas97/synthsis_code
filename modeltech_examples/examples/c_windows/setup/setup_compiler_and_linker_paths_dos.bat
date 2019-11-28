@echo off
rem Check if running 64-bit version

for /f "delims=" %%i in ('vsim -version ^| findstr /c:"vsim"') do set vsim_ver=%%i

set vsim_ver1=%vsim_ver%
set vsim_ver1=%vsim_ver1:-64=%
if "%vsim_ver%"=="%vsim_ver1%" (
	set is64bit=0
) else (
	set is64bit=1
)

if exist C:\WINDOWS\system32\reg.exe goto :reg_okay
else
    echo Could not find reg.exe in the PATH. Set C:\WINDOWS\system32 in the PATH.
	exit /b 1

:reg_okay
rem Check if the system has "VisualStudio" or "VCExpress" installed.

if %is64bit%==1 (
	set NodeDir=Wow6432Node\
)

C:\WINDOWS\system32\reg.exe query "HKLM\SOFTWARE\%NodeDir%Microsoft\VisualStudio\12.0\Setup\VC" /v ProductDir > NUL 2>&1
if errorlevel 0 set VCEDITION=VisualStudio
if errorlevel 1 set VCEDITION=VCExpress

for /f "tokens=2* delims=	 " %%a in ('C:\WINDOWS\system32\reg.exe query "HKLM\SOFTWARE\%NodeDir%Microsoft\%VCEDITION%\12.0\Setup\VC" /v ProductDir') do set TOOLPATH="%%b"
if %is64bit%==1 (
	call %TOOLPATH%\vcvarsall.bat x64
) else (
	call %TOOLPATH%\vcvarsall.bat x86
)
