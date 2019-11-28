#
# Radix definition for State machine states.
# Used to display state values in wave window instead of numeric values.
#
radix define States {
    11'b00000000001 "IDLE" -color orchid,
    11'b00000000010 "CTRL" -color "slate blue",
    11'b00000000100 "WT_WD_1" -color yellow,
    11'b00000001000 "WT_WD_2" -color yellow,
    11'b00000010000 "WT_BLK_1" -color salmon,
    11'b00000100000 "WT_BLK_2" -color salmon,
    11'b00001000000 "WT_BLK_3" -color salmon,
    11'b00010000000 "WT_BLK_4" -color salmon,
    11'b00100000000 "WT_BLK_5" -color salmon,
    11'b01000000000 "RD_WD_1",
    11'b10000000000 "RD_WD_2",
    -default hex,
    -defaultcolor "blue"
}

radix define Opcodes {
    0 "nop" -color "light blue",
    1 "ctrl" -color yellow,
    2 "wt_wd" -color orange,
    3 "wt_blk" -color #ff5522,
    4 "rd_wd" -color #5e68e9,
    4'b(????) "Illegal: %1" -color red,
    -default hex,
    -defaultcolor "grey",
}
