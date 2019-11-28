
Objective
---------
This tutorial is designed to show you the most basic aspects of the Direct
Programming Interface (DPI) for SystemVerilog.  After studying this tutorial, 
you should have a good feel for the basic requirements in using DPI and have 
a good understanding of the interface's intentions.

Release
-------
This tutorial is designed to work with ModelSim/QuestaSim 6.1 releases.

Design/Simulation Details
-------------------------
In order to develop a good understanding of how DPI works in ModelSim/QuestaSim, we will
start with a very small design that simply shows how simulation control flows
back and forth across the boundary between Verilog simulation and code written
in a foreign language.  In this tutorial we will use code written in C, which is
the foreign language most commonly used to interface with Verilog simulation.

The tutorial will be a short, simple simulation which mimics a traffic
intersection.  We will bring up the design in ModelSim/QuestaSim and monitor the
waveform of a signal that represents a traffic light.  We will step through
simulation and watch how the light changes color as we call functions written
in both Verilog and C, freely moving back and forth between the two languages.

Before getting started, let's take a look at the main design source file in
order to get acquainted with the simulation flow and some of the basic
requirements for DPI.

	(open test.sv)

Line 1 -> We have just one top-level module called "test" in which all the
simulation activity will occur.

Line 3 -> We take advantage of a new SystemVerilog capability in which we
declare a new data type called "traffic_signal" and allow it to contain the
data values RED, GREEN, and YELLOW.

Line 5 -> We declare an object of this new traffic_signal type and give it the
name "light".

Lines 7-11 -> We define a Verilog function called "sv_GreenLight" which has no
return value.  It simply sets the light to a value of GREEN.  Note also that
we give the function name a prefix of "sv_" in order to distinguish between
tasks/functions defined in SystemVerilog and functions defined in C.

Lines 13-17 -> Another function called "sv_YellowLight" which changes the
light to YELLOW.

Lines 19-23 -> Another function called "sv_RedLight" that changes the light to
RED (you should get the idea now).

Lines 25-29 -> A Verilog task called "sv_WaitForRed" which simply delays for
10 time units (ns by default).  Why a task all of the sudden instead of a
function?  This will become apparent as we go through the actual simulation
steps coming up.

Lines 31-33 -> Now here's something new that doesn't look like typical Verilog
code.  These lines start with the keyword "export", followed by some
additional information.  The statements you see on these lines are referred to 
as "export declarations".  An export declaration is the basic mechanism used to
inform the Verilog compiler that something needs to be handled in a special
way.  In the case of DPI, the special handling means that the specified task
or function will be made visible to a foreign language and that its name will
need to be placed in a special name space.  The syntax for these declarations
is defined in the SystemVerilog LRM, and there is a simple rule to remember 
regarding how they work:  When running a SystemVerilog simulation and using DPI 
in order to utilize foreign (C) code, the Verilog code should be thought of as 
the center of the universe (i.e. everything revolves around the Verilog code).  
When you wish to make something in Verilog visible to the foreign world, you 
need to "export" it to that world.  Similarly, if there is something from that 
foreign world that you want your Verilog code to see and have access to, you 
need to "import" it to Verilog (see the next section).  So in these lines, what 
we do is export two of the functions and the task that we've just defined to the 
foreign world (sv_YellowLight, sv_RedLight, and sv_WaitForRed).  But why not the
sv_GreenLight function?  ...  You'll see.

Line 35 -> As we mentioned in the previous section, we need to "import" code
from the foreign (C) world into the Verilog world.  The import declaration is 
used to accomplish this.  The additional information you need to supply with an
import declaration includes how you want this foreign code to be seen by Verilog 
(i.e. should it be considered a task or a function), and of course the name of
the task or function.  In this case, we will import a task named "c_CarWaiting" 
from the C world (note the "c_" prefix so that we can keep track of where these 
tasks/functions originated).  This is an important concept to remember.  If you 
try to call a foreign task/function but forgot to include an import declaration 
for it, you will get an error when you load simulation stating that you have an 
unresolved reference to that task/function.

Lines 37-42 -> Here is where the rubber hits the road (no pun intended).  We
just have a little initial block which executes the simulation and walks us
through the light changing scenario.  The light starts out RED by default,
since that is the first (left-most) value in the light's type definition (i.e.
the traffic_signal type).  When simulation starts, we wait for 10 time units
and then change the light to GREEN via the sv_GreenLight function.  All this
occurs in the Verilog world, so there is no need to export the sv_GreenLight 
function.  We won't be doing anything with it over in the foreign world.  
Next, we wait for 10 time units again and then do something called 
"c_CarWaiting".  Well, from our previous discussion of the import declaration,
we now know that this is a C function that will be imported as a Verilog task.  
So when we call this task, we are actually stepping over into the foreign world 
and should be examining some C code.  In fact, let's now take a look at the
other source file in this tutorial to see what will happen when this line 
executes during simulation.

	(open foreign.c)

OK.  There's not too much in this file.  First you see the function definition
for c_CarWaiting.  It has a void return, since we will not be returning
anything to the Verilog world, and no arguments.  The first statement inside
the function simply prints out a little message indicating that a car is
waiting on the other side of the intersection and that we should initiate a
light change sequence.  Then we call something named "sv_YellowLight".  But,
wait, this function has an "sv_" prefix.  Aren't we using that naming
convention to signify that this is a SystemVerilog task/function?  You bet it
is.  That is exactly the point.  Even though we are over in the foreign (C)
world now, executing C functions/statements until this function exits and
returns control back over to Verilog, we can indeed call back over to the
Verilog world and execute tasks/functions from that side.  The reason the C 
code knows that sv_YellowLight exists is because we've exported it back in our
Verilog code (remember the export declaration?).  So now in order to follow
along with the simulation, you should step back over into the test.sv file.

In test.sv, what you do now is look up the sv_YellowLight function (on line
13) and see what is going on there.  Fortunately, it is pretty
straightforward.  We just change the light to a value of YELLOW and then pass
control back to the thing that called this function:  back over to foreign.c
and go to the line following the sv_YellowLight function call.

Now we call something named "sv_WaitForRed".  Yep, that's the SystemVerilog
task that was defined in test.sv earlier.  So back over to Verilog we go.

The task is defined on line 25 in test.sv.  Why is it a task now?  We seemed
to make a big deal of that earlier.  Well, look at what we do in this task.
We simply wait for 10 time units.  Since there is time delay associated with
this procedure, it has to be a task.  All the rules associated with tasks and
functions in basic Verilog will also apply if you call them from the foreign
world.  Since we compile the two source files independently (one with a Verilog
compiler and one with a C compiler), the rules of one language will not be known 
to the compiler for the other.  We will not find out about issues like this in 
many cases until we simulate and hook everything together.  Just be aware of this 
when deciding how to import/export things.

Another important fact to make note of here is that when we made this function 
call to sv_WaitForRed(), which we now know is REALLY a Verilog task, we were 
currently sitting in the foreign (C) world.  If for some reason we want to 
consume simulation time, C doesn't know anything about the Verilog design or 
simulation time units or anything like that.  So we would need to make calls 
back over to Verilog in order to perform such operations.  Again, just remember 
which world you are in as you move around in simulation.

Anyway, sv_WaitForRed just burns 10 time units of simulation and then returns
control back over to C.  So we go back over to foreign.c and go down to the
next line of execution.  Here we call sv_RedLight, which you should be able to
guess is a SystemVerilog function that changes the light to RED.  If you look 
up that function in test.sv, that is exactly what occurs.  This is the last 
statement in the c_CarWaiting function in foreign.c.  So now this function exits 
and returns control back over to Verilog.

We now return to line 40 in test.sv, which called this C function in the first
place.  There is nothing else to be done on this line.  So we drop down to the
next line of execution in the simulation.  We wait for 10 time units and then
call the sv_GreenLight function.  If you recall, this function just keeps 
execution in the Verilog world and changes the light back to GREEN.  Then we're 
all done with simulation.

Running the Tutorial
--------------------
A Makefile has been included with this tutorial in order to help you compile
and simulate the design.  Please examine it to see some of the details.  There 
are three targets in the Makefile that take care of everything you will need
(or you can run "make all" to kick off the whole thing all at once):

1) compile - simply invokes the vlog compiler on the test.sv and foreign.c source file.

2) sim - invokes the simulator using "test" as the top-level module.

Once in simulation, the easiest thing to do would be to simply run in 10 ns
increments and observe the changes in the signal light's waveform.  If you
look in the Objects window in ModelSim/QuestaSim, you should see the "light" object with
its initial value of RED.  Go ahead and drop that object into a Wave window
and you can watch as it changes values at the appropriate simulation times.
Keep track of where you are in the source files as you step through
simulation.  Feel free to experiment and try adding your own functions, tasks,
statements, etc.

Summary
-------
Hopefully this tutorial has helped you to understand the basics of how DPI
works in ModelSim/QuestaSim.  You should feel comfortable with these elements before
moving on to the next tutorial.  This design only accomplishes some simple
function calls to change the values of the signal light in order to stress how
easy it is to step back and forth between Verilog and a foreign language like
C.  However, we have not done anything terribly interesting in regard to
passing data from one language to the other.  Is this possible?  Most
definitely.  In fact, the next tutorial will address this subject.

Notes
-----
If you would like to run this tutorial in a ModelSim/QuestaSim 6.0 environment, 
you will only need to make one change in the test.sv source file (in four places,
though).  In the export and import declarations on lines 31, 32, 33, and 35,
please change "DPI-C" to "DPI".  Due to further qualification of the language
standards, it was determined that "DPI" would not suffice in the long run.
Other foreign languages may eventually be supported and further clarification
of this directive needed to be added.  The 6.1 releases were enhanced to support
this new form of directive.  After making this change, everything will run in 
6.0 releases as it previously did.
