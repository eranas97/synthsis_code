#Copyright 1991-2016 Mentor Graphics Corporation
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

###
## queue_lengths
##
##	When the length of the queue changes, display
##	the sum of two queue lengths.
##
##
proc queue_lengths {w x y} {
 
  catch {destroy $w.queues}
  frame $w.queues
 
  # Build the display for East/West.
  frame $w.queues.ew

  label $w.queues.ew.l -text "east-west traffic waiting:  "
  label $w.queues.ew.e -text 0
  when {/queue_e/current_count'event or /queue_w/current_count'event} {
	set count_val [expr [examine -radix decimal -value /queue_e/current_count] + \
			    [examine -radix decimal -value /queue_w/current_count]]
	.traffic.i.queues.ew.e configure -text $count_val
  }
  pack $w.queues.ew.l $w.queues.ew.e \
	-side left -anchor w -in $w.queues.ew 
 

  # Build the display for North/South.
  frame $w.queues.ns


# **********************  ModelSim EXAMPLE  *************************


#  ADD THE CODE BELOW FOR THE SOLUTION **********************

  label $w.queues.ns.l -text "north-south traffic waiting:  "
  label $w.queues.ns.e -text 0
  when {/queue_n/current_count'event or /queue_s/current_count'event} {
	set count_val [expr [examine -radix decimal -value /queue_n/current_count] + \
			    [examine -radix decimal -value /queue_s/current_count]]
	.traffic.i.queues.ns.e configure -text $count_val
  }

  pack $w.queues.ns.l $w.queues.ns.e \
	-side left -anchor w -in $w.queues.ns 

#  ADD THE CODE ABOVE FOR THE SOLUTION **********************

  pack $w.queues.ns $w.queues.ew -side top -in $w.queues
  $w.c create window $x $y -window $w.queues
 
}


proc draw_queues {} {
  queue_lengths .traffic.i 4c 16c
}















