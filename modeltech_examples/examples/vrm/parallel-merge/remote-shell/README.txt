MULTI-CORE LOCAL EXECUTION

This details how to use the parallel merge facility using examples. All
the parameters detailed in the README in the directory above are not special
parameters to the merge process, but VRM parameters that can be changed on
the command line using the -G switch of VRM. Their default values can
also be changed within the parallel-merge.rmdb file itself it you wish
to tailor the merge process and not want to constantly over-ride the
parameters from the command line.

This example has an extra rmdb file that can be used to generate as many
UCDB files as needed to test the set-up. By defining the NUMTESTS
parameter the tests will be run with a random result. This allows the
feature of only merging passes or failures to be show. To generate the
tests use the following command, setting the NUMTESTS to the number of
UCDBs you want to generate.

vrun generate -rmdb ../generate.rmdb -GNUMTESTS=145

This will generate 145 UCDB files in the sub-directories of VRMDATA/generate
each named Test~XX/Test~XX.ucdb, these can be used to test the parallel
merge process.
It is a requirement that the list of hosts that the rsh commands are going
to be run should be able to run a remote shell. If the rsh command doesn't
run successfully then the system administrator will need to ensure 
the systems are set-up to support the rsh command. The HOSTNAMES parameter
needs to be set to a list of hostnames that are to be used separated by a
space. The process will look into current directory and recursively search
for all the UCDB files called Test*.ucdb and create a file that has
only the UCDBs files that have their TESTSTATUS passed from the search.

There are two time-out settings and care should be taken to ensure that
they are adjusted so that they do not kill the merge process before it
has finished. One of the in-built functions of VRM is to manage the
time it takes to queue an action and the time it takes to run an action.
If either of these times become greater than the time-out maximums then
VRM will take action to clear up the actions that it believes have
errored having gone over the expected time periods. The first time-out
is called QUEUETIMEOUT and is set to 6000 seconds, this is the time
between VRM launching the action and it actually starting. When executing
actions locally or remote shell this time-out would normally be pretty 
small because its the start-up delay. When running on a grid this needs 
to be adjusted to be take into consideration the amount of time the job
would sit in the load sharing queue before the action is started. This 
start is variable on any grid and will depend on loading etc. The second
time-out is called MERGETIMEOUT and is set to 6000 seconds, this is the
time it takes to complete a single merge process i.e the time between the
merge action starts and finishes. This time-out needs to be set to the
time of a single process merge plus some small buffer of time. These
time-outs can be set in the RMDB or set using the -G switch i.e 
-GMERGETIMEOUT=10000 would set the MERGETIMEOUT to 10000 seconds.

vrun merge -GMODE=rsh -rmdb $QUESTA_INSTALL/vm_src/parallel-merge/parallel-merge.rmdb -GHOSTNAMES="dvtvnc10 dvtvnc11 dvtvnc12 dvtvnc13" -GFILELIST=mylist.txt -GTESTSTATUS=passed

It is possible to run more than one job on a single machine by repeating 
the hosts name in the HOSTNAMES parameter. For example the following will
allow 2 jobs to run on two hosts i.e.

vrun merge -GMODE=rsh -rmdb $QUESTA_INSTALL/vm_src/parallel-merge/parallel-merge.rmdb -GHOSTNAMES="dvtvnc10 dvtvnc11 dvtvnc10 dvtvnc11" -GFILELIST=mylist.txt -GTESTSTATUS=passed
