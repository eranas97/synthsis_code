This example shows the following SystemVerilog features:

    * Queues
    * Queue methods

The example is a simple FIFO that is modeled with a SystemVerilog queue.  The
width and depth of the FIFO are controlled using parameters.  Pushing and
popping data in and out of the FIFO as well as checking the number of elements
in the FIFO is done using queue methods.

The queue is also modeled using SystemVerilog 2-state int and bit types.
Where bus contention and net resolution are not a concern, 2-state types can
improve performance.

The testbench for the FIFO contains some simple assertions.  These assertions
verifying that the FIFO is not written when FULL and read when EMPTY.  For
users that do not wish to use assertions, the assertions can be disabled by
removing the +define+ASSERT from the vlog compile line in run.do.
