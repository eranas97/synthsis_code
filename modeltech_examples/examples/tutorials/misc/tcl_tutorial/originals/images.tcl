#Copyright Mentor Graphics Corporation 2005
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

###
## newtop
##
##	Called like: "newtop .i"
##	Creates a new "toplevel" widget.
##	Returns something like .i0, .i1, ... .i99
##
#
proc newtop { base } {
	
	set count 0 
	while {[winfo exists $base$count]} {
		incr count
	}
	set top [toplevel $base$count]
	return $top
}

###
## viewfile
##
##	Show the contents of a file on the screen.
##
#
proc viewfile { filename {ro ""}} {

	if { [file exists $filename] } {
		if { "$ro" == "read_only" } {
			notepad $filename 1
		} else {
			notepad $filename 0
		}

	} else {
		# File doesn't exist. Don't edit it.
		return;
	}

}
###
## images:
#
#	Build a button for each gif in the
#	current directory. When the cursor
#	enters the button print the image name.
#	When the button is pushed, print the
#	"widget" name of the button.
#

proc image_example {} {

	global columnheight imageheight
	global columnheight

	# Set the directory where the images are.
	# (Assumes we are running this from ".")
	set dir ./images
	# Get a list of the images
	set images [glob $dir/*.gif]

	set imagecount 0	;# How many total images.
	set columncount 0	;# How many columns.
	set columnheight 0	;# How high the current column is.


	# Create a new toplevel widget
	set t [newtop .i] 

	# Put the destroy button on the bottom.
	button $t.quit -text "Destroy" -command "destroy $t"
	pack $t.quit -side bottom -fill x

	# Put the view button on the bottom 
	#  (above the destroy button)
	button $t.view -text "See Source Code" \
		-command "viewfile images.tcl"
	pack $t.view -side bottom -fill x

	###
	## Build the frames and buttons.
	## Each column has its own frame.
	## Put each image in its own button.
	#
	foreach imagefile $images {

		# Create a "image" for each gif file
		image create photo image$imagecount \
			-file $imagefile
		set imageheight [image height image$imagecount]

		# If this image makes the column too high,
		#  create a new column and put the image in the
		#  new column. 
		if { [toohigh] } {
			set frame [newframe $t $columncount]
			incr columncount
			set columnheight $imageheight 
		} else {
			incr columnheight $imageheight 
		}

		# Define the button.
		set b [button $frame.b$imagecount \
			-image image$imagecount]
		$b configure -command "pushme $b"

		# Define a "callback" so that
		#  when the cursor enters the button, the 
		#  name of the image is printed on stdout.
		bind $frame.b$imagecount \
			<Any-Enter> [list puts "$imagefile"]

		pack $frame.b$imagecount
		incr imagecount
	}
}


###
## proc newframe
#
# Build a new frame. Each frame 
#  holds 1 column of buttons.
#
proc newframe { parent counter } {

	set frame [frame $parent.frame$counter]
	pack $frame -side left

	return $frame
}


# **********************  ModelSim EXAMPLE  *************************
###
## pushme 
#
# 	Implement a button that prints its
#	parameter on the standard output.
#

# UNCOMMENT THE CODE BELOW TO ADD 'PUSHME' ********************************

#proc pushme { objectname } {
#	puts "Object pushed = $objectname"
#}


# UNCOMMENT THE CODE ABOVE TO ADD 'PUSHME' ********************************

###
## proc toohigh
#
# Return 1 if there are no column frames yet or
# if the current column would be too high for
# the display if this image was added. 
#
# Return 0 otherwise.
#
proc toohigh {} {
	global columnheight imageheight
	global columnheight

	# 700 is an arbitrary limit that looks good.
	if { ([expr $columnheight + $imageheight] > 700) } {
		return 1
	}
	if { $columnheight == 0 } {
		# special case for the first image in a column.
		return 1
	}
	return 0
}






























