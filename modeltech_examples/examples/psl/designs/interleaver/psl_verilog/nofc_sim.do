onerror {resume}
set PrefMain(colorizeTranscript) 1
log -r *
view assertions
view wave
assertion fail -action break -r *
do nofc_wave.do
