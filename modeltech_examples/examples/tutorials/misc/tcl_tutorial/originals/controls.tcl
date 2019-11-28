#Copyright Mentor Graphics Corporation 2005
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

###
## Controls 
##
##	Create two sets of control widgets.
##
##	The first widget controls the inter-arrival times
##	of cars arriving at the lights.
##
##	The second widget controls the length of the lights.
##

proc draw_controls {} {
  traffic_controls .traffic.i 13c 6c
  light_controls   .traffic.i 4c  7c
}
 
###
## traffic_controls
##
##	Given an object name and (x,y) coordinates,
##	build and display a set of controls, one per
##	parameter.
##	
##	The parameters are the VHDL signals that 
##	determine the length of time BETWEEN cars
##	arriving at the light. (Really arriving in the queue).
##
proc traffic_controls {w x y} {

  catch {destroy $w.traffic_controls}

  frame $w.traffic_controls

  # East/West traffic controls
  
  scale $w.traffic_controls.ew \
	-label "east/west inter-arrival time" \
        -from 1 -to 100 -length 8c -orient horizontal \
        -command "set_time_variable /ew_arrival_rate"
  pack $w.traffic_controls.ew \
       -side top 
  $w.traffic_controls.ew set 40


  # North/South traffic controls


# **********************  ModelSim EXAMPLE  *************************

  
# ADD THE CODE BELOW FOR THE SOLUTION *******************************

#   scale $w.traffic_controls.ns \
#	-label "north/south inter-arrival time" \
#        -from 1 -to 100 -length 8c -orient horizontal \
#        -command "set_time_variable /ns_arrival_rate"
#
#  pack $w.traffic_controls.ns \
#       -side top 
#  $w.traffic_controls.ns set 40

# ADD THE CODE ABOVE FOR THE SOLUTION *******************************
  
  
  # Don't forget to PACK your widget!

  # Also, don't forget to initialize the slider. Try 40.

  
 

  $w.c create window $x $y -window $w.traffic_controls

}

###
## light_controls
##
##	Given an object name and (x,y) coordinates,
##	build and display a set of controls, one per
##	parameter.
##	
##	The parameters are the VHDL signals that 
##	determine the length of each light (red, yellow, green).
##
 
proc light_controls {w x y} {

  catch {destroy $w.light_controls}

  frame $w.light_controls

  # East/West light controls
  
  scale $w.light_controls.ew_g \
	-label "east/west green time" \
        -from 1 -to 100 \
	-length 6c \
	-orient horizontal \
        -command "set_time_variable /ew_green_time" 
  scale $w.light_controls.ew_y \
	-label "east/west yellow time" \
        -from 1 -to 100 \
	-length 6c \
	-orient horizontal \
        -command "set_time_variable /ew_yellow_time" 
  $w.light_controls.ew_g set 30
  $w.light_controls.ew_y set  5
  pack $w.light_controls.ew_g $w.light_controls.ew_y -side top


  # North/South light controls
  
# ADD THE CODE BELOW FOR THE SOLUTION *****************************************  
  
#  scale $w.light_controls.ns_g \
#	-label "north/south green time" \
#        -from 1 -to 100 \
#	-length 6c \
#	-orient horizontal \
#        -command "set_time_variable /ns_green_time" 
#  scale $w.light_controls.ns_y \
#	-label "north/south yellow time" \
#        -from 1 -to 100 \
#	-length 6c \
#	-orient horizontal \
#        -command "set_time_variable /ns_yellow_time" 
#  $w.light_controls.ns_g set 30
#  $w.light_controls.ns_y set  5
#  pack $w.light_controls.ns_g $w.light_controls.ns_y -side top
  
  
# ADD THE CODE ABOVE FOR THE SOLUTION *****************************************

  # Build TWO scale widgets like the East/West widgets.

  # Initialize your widget!

  # Pack your widget.



  # Red light control
  
  scale $w.light_controls.b_r \
	-label "both red time" \
        -from 1 -to 100 \
	-length 6c \
	-orient horizontal \
        -command "set_time_variable /both_red_time" 
  $w.light_controls.b_r  set  2
  pack $w.light_controls.b_r -side top
 

  $w.c create window $x $y -window $w.light_controls
 
}
 

###
## set_time_variable
##
##	Given a VHDL time signal and an integer value,
##	force it to nanoseconds.
##
proc set_time_variable {var val} {

  force -freeze $var $val ns

}








