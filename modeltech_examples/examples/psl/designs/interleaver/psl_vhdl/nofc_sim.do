onerror {resume}
set PrefMain(colorizeTranscript) 1
set StdArithNoWarnings 1
set NumericStdNoWarnings 1
log -r *
view assertions
assertion fail -action break -r *
view wave
do nofc_wave.do
