Objective
---------
This tutorial is designed to build on your understanding of the Direct
Programming Interface (DPI) for SystemVerilog.  In the first tutorial, you
were shown the basic elements of the interface and how to make simple
function calls to/from Verilog and C.  However, no data were passed across the
boundary, which is a very important topic to understand.  This tutorial will
focus on that aspect of the interface.

Release
-------
This tutorial is designed to work with ModelSim 6.0 releases.  Minor syntactic
changes are required for use with ModelSim 6.1 (see Notes).

Preliminary Information
-----------------------
Although DPI allows Verilog to interface with any foreign language, we will
concentrate on the C language in this tutorial.  However, keep in mind the 
fact that other foreign languages may eventually be used.

Whenever we want to send the value of an object from Verilog to C, or vice
versa, that value will have a dual personality.  It may have been initialized
as a bit or a reg over in the Verilog world, for example, and then passed over
to C via an imported function call.  A thought should now enter your
head:  "Hey, wait, C doesn't have reg's and bit's and logic vectors and things
like that.  How's this going to work?"

What you basically need in this situation is a table that maps Verilog types to 
C types.  Fortunately, much of the type definition that went into Verilog-2001
and SystemVerilog was done with the intention of matching C data types.  So,
much of this mapping is pretty straightforward.  However, some of the mapping
is a little more complex, and you will need to be aware of how an object in
Verilog will map to its counterpart in C.

Do you have to define this mapping?  No.  The SystemVerilog language defines 
it for you, and the simulator is set up to handle all of these dual 
personality issues itself.  A little inside information on the type mapping 
should help you grasp this concept.

Let's start with a simple Verilog type like "int".  In Verilog, an int is a
2-state, signed integer that is stored in 32 bits of memory (on the system;
it's not an array or a vector).  The fact that a Verilog int is a 2-state type
is important in that it only allows 0 and 1 values to be assigned to its bits.
In other words, no X or Z values are allowed (they are just converted to 0 if
you try to assign them).  OK, this all sounds pretty simple and it appears to
behave just like a C int would.  So the mapping is easy:  a Verilog int will
map to a C int as it crosses the boundary.

The best thing to do now would probably be to start running some example data
through the simulator and to take a good look at exactly what happens.  So
let's fire up the tutorial design in ModelSim and have at it.

Running the Tutorial
--------------------
A Makefile has been included with this tutorial in order to help you compile
and simulate the design.  Please examine it to see some of the details.  There 
are three targets in the Makefile that take care of everything you will need
(or you can run "make all" to kick off the whole thing all at once):

1) compile - simply invokes the vlog compiler on the test.sv and foreign.c source file.

2) sim - invokes the simulator using "test" as the top-level module. 

Once in simulation with the "test" module loaded, you can use the "step -over"
command/button to advance through simulation.  We will simply be setting
values of different types of Verilog objects and sending the data over to C 
for print out to the screen.

With the first step, you should be on line #12 in test.sv where we print out
the value of "int_var", which is defined as an "int" on line #6.  Nothing has been
assigned to int_var yet, so it should have its default initial value of 0.  If you 
look in the Objects window, you should see that int_var is indeed equal to 0.  Go
ahead and do another step, which will call our imported C function "print_int" 
with int_var as its input parameter.  If you look in the Transcript window after this 
line executes, you should see the following message:

	Just received a value of 0.

That's what we expected to happen.  So far, so good.

Next we set int_var to a value of 1.  Go ahead and do a step and you will see the
value of int_var change to 1 in the Objects window.  Now do another step and you
should see a 1 being printed in the Transcript window this time.  With the
next two steps, we change int_var to -12 and print again.  You should get the idea
now.  Both positive and negative integers are getting set and printed properly.

Next we are going to use the print_int function to print the value of bit_var, which
is defined as a "bit" type on line #7.  It also has a default initial value of
0, so you can guess what will be printed out.  Do a step and verify the results
in the Objects window and in the Transcript window.

Next we set bit_var to a 1 and print.  No problem.

Next we set bit_var to X and print.  But look in the Objects window after you do the 
first step.  It didn't go to X.  It went to 0.  Ahhh.  Remember that the bit 
type is a 2-state type.  If you try to assign an X or a Z, it gets converted to
0.  So we get a 0 instead, and that's what should get printed.  Do a step for the 
print_int function and verify.

Now let's try some 4-state values.  We should be on line #22 now where logic_var is being
assigned a 1.  logic_var is an object of type "logic", which is a 4-state type.  Do a step and you 
should see the value of logic_var change from X to 1 in the Objects window.  Next we call 
print_int again to print the value out.  Do a step and verify the result.

Next we set logic_var to X.  Do a step to change this value.  Now do another step to print
it.  Woh!  A value of 0 got printed instead of the X.  Why is that?  We need to 
stop simulating for a bit and go diving into some source code to see what happened.

Open up the foreign.c file, which is the C source for our imported functions.
Look for the print_int function and look at its parameter.  It is expecting an
int as its input.  That works fine when we were sending over int's in the
first place.  But now we are working with 4-state data types.  So we can have
X and Z values.  How is that kind of data going to cross over the boundary, and 
what is it going to look like when it gets over to C?  What about user defined 
types and the many other types of data we can send back and forth?  How are you 
supposed to know how to write your C functions to accept that kind of data properly 
and/or send it back to Verilog properly?

Well, those are a lot of questions to answer.  Fortunately, the answer is that
you don't really have to know the gory details.  The SystemVerilog language
defines this data mapping for you.  Furthermore, ModelSim will create a C
header file for you on the fly during compilation that you can reference in
your C code.  All the function prototypes, data type definitions, and other
important pieces of information are made available to you via this header
file.

First, look in the Makefile and find the "compile" target which compiles the
Verilog source file.  Notice that there is a new option with the vlog command
called "-dpiheader" with an output file name as its argument.  As vlog
compiles your Verilog source file, should it come across any DPI import/export 
statements, it will analyze those statements and create a C header file for you 
with what it knows to be the correct way to define the prototypes for your
imported/exported functions/tasks.  In this tutorial, we call the file
"dpi_types.h".

Now, open up the dpi_types.h file and look around for familiar things.  At the
top you will see some unfamiliar stuff that is there for internal DPI
purposes.  But if you go down to the bottom, you should see a function
prototype for our print_int function.  As expected, the input parameter is an
int type.

OK, now look just below this function and you should see the prototype for
another function called "print_logic".  This one has an input parameter of
type "svLogic" (i.e. SystemVerilog Logic).  What is that you might say?  Well,
we don't want to get too deep into the details.  But if you are interested,
this file #include's another header file called "svdpi.h", which is actually
part of the SystemVerilog language and is shipped in the ModelSim installation
directory (that's why we have "-I$(QUESTA_HOME)/include" on the command line for
C compilation in the Makefile's "foreign" target).  You can take a look at
that file if you'd like, or you can read more about it in the SystemVerilog
LRM.  But that is not important right now.  All you need to know is that the
svLogic type is basically an unsigned char.

You don't even really need to know that.  As long as you #include dpi_types.h in your
C source file, all these function prototypes and data types will be made
available to you.  In fact, we strongly recommend that you use this file when
writing the C code that will interface with Verilog via DPI.

So take a quick look back at the test.sv file and look for the DPI import
statements.  There is one for print_int and one for print_logic.  The vlog
compiler looks at these statements, sees the names of the functions being
imported along with their parameters and return values (in Verilog terms), and
then it creates the correct DPI header file for you.  In the case of the
print_logic function, it saw that the input parameter was of type "logic". So it
put logic's counterpart of "svLogic" in the header file.  Now both elements of
the dual personality for this particular object are defined and everything
should pass over to C properly.

Let's go back to simulation.  We should be on line #26, just after the
point where the bad logic value of 0 got printed instead of an X.  Now that we
know we were using the wrong function for this particular type of data, we
will use the "print_logic" function instead.  Go ahead and do another step to
execute this line.  OK, we got our X value printed out this time.  You can
take a look at the foreign.c file to see how this was accomplished.
Basically, 4-state values are represented as 0, 1, 2, and 3 in their canonical
form.  The values you see in the switch statement inside the print_logic
function are #define'd in the svdpi.h file for you so that you can keep
everything straight.  Again, if you use the DPI header file in your C code,
you can just use this stuff and everything will work out properly.

So go ahead and step through a few more statements and you can see that
logic_var gets
set to some other 4-state values and we print them correctly using the
print_logic function.

Summary
-------
There is certainly much more involved with passing data back and forth
across the boundary between C and Verilog using DPI.  What about user-defined
types?  What about arrays?  Structs?  64-bit integers?  This particular
subject can get into some pretty hefty detail, and we've already covered quite
a bit here.  Hopefully this tutorial has helped you understand the most basic
things to be aware of regarding passing data through the interface.  Most
important of all, to make use of the DPI header file that vlog creates for you
in order to make sure your C code is written properly to interface with
SystemVerilog.

Notes
-----
If you would like to run this tutorial in a ModelSim 6.1 environment, you will
only need to make a couple of changes in the test.sv source file.  In the import 
declarations on lines 3 and 4, please change "DPI" to "DPI-C".  Due to further 
qualification of the language standards, it was determined that "DPI" would not 
suffice in the long run.  Other foreign languages may eventually be supported and 
further clarification of this directive needed to be added.  After making this 
change, everything else will run as previously described.
