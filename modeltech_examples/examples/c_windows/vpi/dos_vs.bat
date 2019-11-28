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
rem Simple VPI Example - Simulation DOS shell script
rem
rem Usage:     Help/Usage ..................... dos_vs.bat
rem            Run VPI example ................ dos_vs.bat run
rem            Clean directory ................ dos_vs.bat clean
rem
rem NOTE: This script is intended to be run in a DOS shell.
rem

SETLOCAL
if "%1"=="clean" goto :call_clean
if not "%1"=="run" goto :print_usage

if exist work (
	rmdir /S /Q work 2> nul
)

rem Create the library.
for %%i in (vlib.exe) do  (
	if exist "%%~dp$PATH:i" (
		set PLATFORM_INSTALL_HOME=%%~dp$PATH:i
		vlib.exe work
	) else (
    	echo "ERROR: Couldn't run vlib.exe. Please set your PATH to contain the ModelSim/QuestaSim executables."
		goto ::exit_setup
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

rem  Compile and link the C files using Visual C++
echo cl -c -Ox -Oy -I%INSTALL_HOME%include vpi_test.c
cl -c -Ox -Oy -I%INSTALL_HOME%include vpi_test.c
echo link /DLL -export:vlog_startup_routines vpi_test.obj %PLATFORM_INSTALL_HOME%\mtipli.lib
link /DLL -export:vlog_startup_routines vpi_test.obj %PLATFORM_INSTALL_HOME%\mtipli.lib

rem Compile the HDL sources.
vlog prim.v dff.v top.v

rem Simulate the design
vsim -c -do vsim.do top -pli vpi_test.dll
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
    echo ### Run VPI example ................ dos_vs.bat run
    echo ### Clean directory ................ dos_vs.bat clean
    echo ###
	goto :done

:done
	ENDLOCAL
