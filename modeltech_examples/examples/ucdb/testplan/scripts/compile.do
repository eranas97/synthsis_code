vlib work
vcom -cover sbectf src/Arb.vhd
vcom -cover sbectf src/Fifo.vhd
vcom -cover sbectf src/Fs_add.vhd
vcom -cover sbectf src/Micro.vhd
vcom -cover sbectf src/Modetwo.vhd
vcom -cover sbectf src/Post.vhd
vcom -cover sbectf src/Pre.vhd
vcom -cover sbectf src/Tx.vhd
vcom -cover sbectf src/bd4st.vhd
vcom -cover sbectf src/bt4r.vhd
vcom -cover sbectf src/concat.vhd
vcom -cover sbectf src/schmitt.vhd
vcom -cover sbectf src/testarb.vhd
vlog -cover sbectf -sv +acc=g src/testconcat.sv
