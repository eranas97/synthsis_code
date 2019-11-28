#Copyright Mentor Graphics Corporation 2005
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

###
## State Machine Animation.
##
##	Draw a crude state diagram. 
##	Connect to the simulation - when the
##	simulation state changes, change the
##	state diagram.
##
#

###
## draw_state_machine
##
##	Draw circles to represent the simulation
##	states: green_ew, green_ns, yellow_ew, yellow_ns,
##	and both_red.
##
##	Draw arcs between the states at the right place.
#
proc draw_state_machine {} {
	global stateinfo

	catch { destroy .state_machine }
	catch { unset stateinfo }

	set t [toplevel .state_machine ]
	wm geometry .state_machine  +375+5

	set c [canvas $t.c \
		-width 230 \
		-height 380 \
		-xscrollcommand [list $t.xscroll set] \
		-yscrollcommand [list $t.yscroll set] \
		-scrollregion {0 0 230 380} ]

	# Remember the canvas object handle
	set stateinfo(canvas) $c

	scrollbar $t.xscroll -orient horizontal \
		-command [list $c xview]
	scrollbar $t.yscroll -orient vertical \
		-command [list $c yview]

	pack $t.xscroll -side bottom -fill x
	pack $t.yscroll -side right -fill y
	pack $c -side top -fill both -expand true

	# East-West
	set stateinfo(ew_green,x) 50
	set stateinfo(ew_green,y) 350
	set stateinfo(ew_green,color) green

	set stateinfo(ew_yellow,x) 50
	set stateinfo(ew_yellow,y) 200 
	set stateinfo(ew_yellow,color) yellow

	# North-South
	set stateinfo(ns_green,x) 200
	set stateinfo(ns_green,y) 350 
	set stateinfo(ns_green,color) green 

	set stateinfo(ns_yellow,x) 200
	set stateinfo(ns_yellow,y) 200 
	set stateinfo(ns_yellow,color) yellow

# ******************  ModelSim EXAMPLE part 1 of 3  *******************
# Change the both_red coordinates here. 
# After you change the coordinates of the both_red state you'll need to
# change the transition lines - see *** EXAMPLE part 2 *** below:

	# Both Red Lights
	set stateinfo(both_red,x) 125
	set stateinfo(both_red,y) 50 
	set stateinfo(both_red,color) red

	set states "both_red ew_green ns_green ew_yellow ns_yellow"
	set stateinfo(states) $states 

	# Create the "states" and color them.
	foreach state $states {
		set xc $stateinfo($state,x)
		set x1 [expr $xc - 25] 
		set x2 [expr $xc + 25] 
		set yc $stateinfo($state,y)
		set y1 [expr $yc - 25]  
		set y2 [expr $yc + 25] 

		# Figure out which color we 
		# should paint for this state.
		set color $stateinfo($state,color)

		set t [$c create oval $x1 $y1 $x2 $y2 \
			-width 4 -fill $color]

		# Save the object handle of state "$state",
		# this handle is used later to change the color
		# of this object.
		set stateinfo($state,object) $t
	}

	
# ******************  ModelSim EXAMPLE part 2 of 3  *******************
# Change the transition arrow positions here.
# To change the active color see *** EXAMPLE part 3 *** below:

	# Draw the state transitions.
	draw_arc $c ew_green  ew_yellow   50 325  50 225
	draw_arc $c ew_yellow both_red    50 175 100  75
	draw_arc $c both_red  ew_green   125  75  75 325

	draw_arc $c ns_green  ns_yellow  200 325 200 225
	draw_arc $c ns_yellow both_red   200 175 150  75
	draw_arc $c both_red  ns_green   125  75 175 325 

	# Uncomment this to print (x,y) coordinates.
	#bind $c <Motion> {puts "%x %y"}

	# Only do this when the simulation is up.
	when { /traffic_light/curr_st } { 
		new_current_state [examine -value /traffic_light/curr_st] 
	}
}

###
## new_current_state
##
##	This is called by the "when" statement when
##	the simulation state changes.
##
#
proc new_current_state { tostate } {
	global stateinfo

	# Change the current state.
	if { [catch {set currentstate $stateinfo(currentstate)} ] } {
		# current state is not set yet.

	} else {
		# Sometime we get called when the tostate is
		#  the same as the currentstate.
		#  We don't care about that.
		if { "$currentstate" != "$tostate" } {

			## 
			# Restore the inactive color.
 
			# Get the handle to the CURRENT state object.
			set t $stateinfo($currentstate,object)

			# Change the color of the state object
			# back to the inactive color. 
			$stateinfo(canvas) itemconfigure $t \
				-fill $stateinfo($currentstate,color)

			##
			# Flash the arc.

			# Get the handle to the arc .
			set t $stateinfo(arc,$currentstate,$tostate)

			# Make it wide.
			$stateinfo(canvas) itemconfigure $t -width 4 
			# Flush the X buffer.
			update

			# Wait a bit.
			after 100

			# Make it thin.
			$stateinfo(canvas) itemconfigure $t -width 2 
			# Flush the X buffer.
			update
		}
	}

	# Get the handle to the NEXT state object.
	set t $stateinfo($tostate,object)


# ******************  ModelSim EXAMPLE part 3 of 3  *******************
# Change the active color here.

	# Change the color of the state object to the 
	# ACTIVE color.
	$stateinfo(canvas) itemconfigure $t -fill black

	# Remember which state we are currently in.
	# If you leave this out, this code doesn't work. 
	set stateinfo(currentstate) $tostate

	# Flush the X buffer for good measure.
	update
}


###
## draw_arc
##
##	Draw a arrow on a canvas from (fx,fy) to (tx,ty)
##	Set some global state transition information.
##
proc draw_arc {c fromstate tostate fx fy tx ty } {
	global stateinfo

	# draw from hotspot to hotspot
	set t [$c create line $fx $fy $tx $ty \
		-width 2 -arrow last]
	set stateinfo(arc,$fromstate,$tostate) "$t"
}











