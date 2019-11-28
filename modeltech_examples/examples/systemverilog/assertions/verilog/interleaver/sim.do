onerror {resume}
set PrefMain(colorizeTranscript) 1
log -r *
run 100us
view assertions
view fcovers
view covergroups
view wave
do wave.do
add wave /interleaver_tester/interleaver1/cover__s_interleave_sm
add wave /interleaver_tester/cover__s_hs_more_10__1
add wave /interleaver_tester/cover__s_hs_less_10__1
add wave /interleaver_tester/cover__s_hs_less_10
add wave /interleaver_tester/cover__s_hs_more_10
assertion enable -off -r *
