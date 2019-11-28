for %%f in (transcript *.so *.o *.wlf core* *.obj *.dll *.h vsim_stacktrace.vstf results.txt *.exp *.lib) do (
	if exist %%f del %%f
)
rmdir /s /q work  2> nul
