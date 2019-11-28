@echo off
rem
rem Copyright 1991-2016 Mentor Graphics Corporation
rem
rem All Rights Reserved.
rem
rem THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
rem MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
rem Compilation and Execution Script for Microsoft Windows Platforms
rem
rem Simple UCDB Example - Simulation DOS shell script
rem
rem Usage:     Help/Usage ..................... dos_vs.bat
rem            Run UCDB example ............... dos_vs.bat run
rem            Clean directory ................ dos_vs.bat clean
rem
rem NOTE: This script is intended to be run in a DOS shell.
rem

SETLOCAL
if "%1"=="clean" goto :call_clean
if not "%1"=="run" goto :print_usage
if exist work (
	rmdir /S /Q work
)

rem Create the library.
for %%i in (vlib.exe) do  (
	if exist "%%~dp$PATH:i" (
		set PLATFORM_INSTALL_HOME=%%~dp$PATH:i
		vlib.exe work
	) else (
    	echo "ERROR: Couldn't run vlib.exe. Please set your PATH to contain the ModelSim/QuestaSim executables."
		goto :exit_setup
	)
)

rem Get the simulator installation directory.
if "%PLATFORM_INSTALL_HOME:~-1%"=="\" set PLATFORM_INSTALL_HOME=%PLATFORM_INSTALL_HOME:~0,-1%
for %%f in (%PLATFORM_INSTALL_HOME%) do (
	set INSTALL_HOME=%%~dpf
)

rem Set the compiler and linker paths.
call %INSTALL_HOME%\examples\c_windows\setup\setup_compiler_and_linker_paths_dos.bat
if errorlevel 1 goto :exit_setup

rem  Compile the HDL source files.
vlog -fsmverbose -cover bsectf -sv test.v
vcom -fsmverbose -cover bsectf test.vhd

rem Simulate the design and create the ucdb file.
vsim -togglenovlogints -coverage -c top -do sim.do

rem  Compile and link the C files using Visual C++
echo cl -c -Ox -Oy -I%INSTALL_HOME%include ucdbdump.c
cl -c -Ox -Oy -I%INSTALL_HOME%include ucdbdump.c

link /OUT:ucdbdump.exe ucdbdump.obj -DEFAULTLIB:%PLATFORM_INSTALL_HOME%\ucdb.lib

rem Run the UCDB application.
echo ucdbdump test.ucdb -o test.dump
ucdbdump.exe test.ucdb -o test.dump
goto :done

:exit_setup
	echo.
	echo Improper environment or Microsoft Visual Studio 12.0 not installed.
	if (%is64bit% == 1) (
		echo Make sure you have Microsoft Visual Studio 12.0 Professional edition installed with the necessary SDK's.
	) else (
		echo Make sure you have Microsoft Visual Studio 12.0 Professional/Express edition installed with the necessary SDK's.
	)
	echo.
	goto :done

:call_clean
	call clean.bat
	goto :done

:print_usage
    echo ###
    echo ### Help/Usage ..................... dos_vs.bat
    echo ### Run UCDB example ............... dos_vs.bat run
    echo ### Clean directory ................ dos_vs.bat clean
    echo ###
	goto :done

:done
	ENDLOCAL
