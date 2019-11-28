#Copyright Mentor Graphics Corporation 2005
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

###
## intersection_example
##
##	Build the intersection and 
##	setup the when statements.
##
#
proc draw_intersection {} {

	# If the old one exists, delete it.
	if {[winfo exists .traffic]} {
		destroy .traffic

		# Probably should take down any "when"
		# statements too. 
        }

	#
	# make a new toplevel and intersection
	# 
	toplevel .traffic
	wm geometry .traffic 725x760+2+2
	build_intersection .traffic.i
	pack .traffic.i

	create_run_buttons .traffic.i

}

proc create_run_buttons { obj } {

	set rb $obj.runsome
	button $rb -command "transcribe run 1000 ns" -text "Run 1000"
	pack $rb
	$obj.c create window 16c 16c -window $rb

	set rb $obj.runall
	button $rb -command "transcribe run -all" -text "Run Forever"
	pack $rb
	$obj.c create window 16c 17c -window $rb

	set rb $obj.break
	button $rb -command "vsim_break" -text "Break"
	pack $rb
	$obj.c create window 16c 18c -window $rb


}

###
## create a traffic light
##
##	Given an object name, create a frame
##	with the given object name. In the frame create
##	a canvas. On the canvas draw a stop light. 
#
proc create_light { obj } {

    frame $obj -relief sunken -height 3c -width 1c
    canvas $obj.c -width 1c -height 3c
    pack $obj.c -fill both

    # Draw the "light bulbs"
    $obj.c create oval 0.1c 0.1c 0.9c 0.9c -fill gray -tag $obj.c.red
    $obj.c create oval 0.1c 1.1c 0.9c 1.9c -fill gray -tag $obj.c.yellow
    $obj.c create oval 0.1c 2.1c 0.9c 2.9c -fill gray -tag $obj.c.green

    return $obj
}

###
## set_light_state
##
## 	Given an object name, and a color, light up the
##	proper "light bulb" with the proper color.
##
##	"color" must be one of "red", "green", or "yellow".
##	"obj" must have been created previously with create_light
##
#
proc set_light_state {color obj} {

    # turn off the old light
    switch $color {
	red {
	  $obj.c itemconfigure $obj.c.yellow -fill gray 
	  $obj.c itemconfigure $obj.c.green -fill gray
        }
	yellow {
          $obj.c itemconfigure $obj.c.green -fill gray
          $obj.c itemconfigure $obj.c.red -fill gray
        }
	green {
          $obj.c itemconfigure $obj.c.red -fill gray
          $obj.c itemconfigure $obj.c.yellow -fill gray
        }
    }

    # turn on the new light
    $obj.c itemconfigure $obj.c.$color -fill $color

    # Flush all the "events" out to the X server.
    update
}

###
## build_intersection
##
##	Given an object name, create a giant canvas, and
##	draws lines representing an intersection.
##	Create two stop lights and put them on the canvas too.
##
#
proc build_intersection { obj } {

    frame $obj -height 20c -width 20c -bg gray -relief flat
    canvas $obj.c -height 20c -width 20c -bg gray -relief flat
    #frame $obj -height 25c -width 25c -bg gray -relief flat
    #canvas $obj.c -height 25c -width 25c -bg gray -relief flat
    pack $obj.c -in $obj

    # draw the  lines that make up the "roads"

    # top-left quadrant
    $obj.c create line 8c 0c 8c 9c
    $obj.c create line 8c 9c 0c 9c
    #$obj.c create line 10c 0c 10c 10c
    #$obj.c create line 10c 10c 0c 10c

    # bottom-left quadrant
    $obj.c create line 0c 14c 8c 14c
    $obj.c create line 8c 14c 8c 21c
    #$obj.c create line 0c 15c 10c 15c
    #$obj.c create line 10c 15c 10c 25c

    # top-right quadrant
    $obj.c create line 13c 0c 13c 9c
    $obj.c create line 13c 9c 21c 9c
    #$obj.c create line 15c 0c 15c 10c
    #$obj.c create line 15c 10c 25c 10c

    # bottom-right quadrant
    $obj.c create line 21c 14c 13c 14c
    $obj.c create line 13c 14c 13c 21c
    #$obj.c create line 25c 15c 15c 15c
    #$obj.c create line 15c 15c 15c 25c

   # embed the traffic lights into the roads
    $obj.c create window 15c 10c \
	-window [create_light $obj.ew_light] \
         -anchor nw -tags ns_light
    $obj.c create window 10c 15c \
	-window [create_light $obj.ns_light] \
         -anchor nw -tags ns_light


    # add intersection sign
    catch {destroy .traffic.i.sign}
	label .traffic.i.sign -text " \nUsing Tcl with [ProductName] [vsimId]\n   \
			-- the intersection of Hollywood & Vines --   \n "
	.traffic.i.c create window 13c 2c \
	-window .traffic.i.sign 

    
}















