for %%f in (transcript *.o *.wlf core* *.obj *.dll *.h vsim_stacktrace.vstf results.txt *.exp *.lib *.dump *.ucdb *.exe  *.manifest) do (
	if exist %%f del %%f
)
rmdir /s /q work  2> nul
