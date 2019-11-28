onerror {resume}
set PrefMain(colorizeTranscript) 1
view wave
log -r *
view assertions
view coverdirectives
fcover configure -enable -weight 4 -at_least 100  /interleaver_tester/interleaver1/c_interleave_sm
fcover configure -enable -weight 4 -at_least 100 /interleaver_tester/c_no_dwn_hs_more_10
fcover configure -enable -weight 4 -at_least 100 /interleaver_tester/c_no_up_hs_more_10
fcover configure -enable -at_least 250 /interleaver_tester/c_no_dwn_hs_less_10
fcover configure -enable -at_least 250 /interleaver_tester/c_no_up_hs_less_10
assertion fail -action break -r *
do forall_wave.do
