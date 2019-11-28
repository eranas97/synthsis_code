onerror {resume}
set PrefMain(colorizeTranscript) 1
log -r *
view assertions
assertion fail -action break -r *
assertion enable -on -r *
view wave
do wave.do
