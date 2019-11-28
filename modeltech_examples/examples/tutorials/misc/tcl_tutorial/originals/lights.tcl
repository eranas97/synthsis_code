#Copyright Mentor Graphics Corporation 2005
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

###
## connect_lights
##
##	When a signal changes in the simulation,
##	change the stop light display.
##
#
proc connect_lights {} {

	if { ![winfo exists .traffic] } {
		puts "Better load the intersection!"
	}

	# Load the VHDL Simulation.
	# Use the "vsim" command with with -lib option.


        #
        # connect light_ew events to the gui
        #
	# Decode the bits of light_ew 
	#	001 = green
	#	010 = yellow
	#	100 = red
	#

	# When the /light_ew signal changes, evaluate
	# this Tcl body.
	# Specifically, test the value of the /light_ew 
	# signal. Set the display light depending on the
	# state of the signal.
	#
        when {/light_ew} { 
          if {[examine -value /light_ew(0)] == 1} { 
            set_light_state green .traffic.i.ew_light 
          } 
          if {[examine -value /light_ew(1)] == 1} {
            set_light_state yellow .traffic.i.ew_light
          }
          if {[examine -value /light_ew(2)] == 1} {
            set_light_state red .traffic.i.ew_light
          } 
        }

	# Add the "ns" when statements similar to the "ew"
	# above.

# **********************  ModelSim EXAMPLE  *************************
	#
        # When the /light_ns signal changes, evaluate
	# this Tcl body.
	# Specifically, test the value of the /light_ns 
	# signal. Set the display light depending on the
	# state of the signal.
	#
# ADD THE CODE BELOW FOR THE SOLUTION ******************************* 
       
#	when {/light_ns} { 
#          if {[examine -value /light_ns(0)] == 1} { 
#            set_light_state green .traffic.i.ns_light 
#          } 
#          if {[examine -value /light_ns(1)] == 1} {
#            set_light_state yellow .traffic.i.ns_light
#          }
#          if {[examine -value /light_ns(2)] == 1} {
#            set_light_state red .traffic.i.ns_light
#          } 
#        }

# ADD THE CODE ABOVE FOR THE SOLUTION *******************************

	# After we have everything setup, put a little
	# reminder in the lower right hand corner...
	catch {destroy .traffic.i.connected}
	label .traffic.i.connected -text "Connected to\nSimulation"
	.traffic.i.c create window 4c 18c \
		-window .traffic.i.connected 
}














