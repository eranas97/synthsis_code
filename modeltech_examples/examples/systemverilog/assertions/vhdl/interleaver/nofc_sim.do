onerror {resume}
set PrefMain(colorizeTranscript) 1
set StdArithNoWarnings 1
set NumericStdNoWarnings 1
assertion fail -action break -r *
log -r *
view assertions
view wave
do nofc_wave.do
