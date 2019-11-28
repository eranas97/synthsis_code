#Copyright 1991-2016 Mentor Graphics Corporation
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

  add wave ld
  add wave rst
  add wave clk
  add wave d
  add wave q
  force -freeze clk 0 0, 1 {50 ns} -r 100
  force rst 1
  force rst 0 10
  force ld 0
  force d 1010
  run 1700
  force ld 1
  run 100
  force ld 0
  run 400
  force rst 1
  run 200
  force rst 0 10
  run 1500


