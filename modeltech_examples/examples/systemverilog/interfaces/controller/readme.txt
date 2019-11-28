This example shows the following SystemVerilog features:

    * Basic interface usage
    * Ports on interfaces
    * Interface modports
    * Tasks & functions in interfaces
    * Assertions in interfaces

The example has a simple memory and a simple controller.  The controller will
perform READS & WRITES from the memory using tasks that are defined in a
SystemVerilog interface.  By doing this, different interfaces can be used
without necessitating changes in either the controller or the memory thus
enabling reuse of components.

The interface also contains a simple assertion.  Assertions in interfaces work
great to verify protocols in the interface are not violated.  In this very
simple case, the assertion is verifying that a READ or WRITE does not occur
before a previous READ or WRITE has finished.  For users that do not wish to
use assertions they can be disabled by removing the +define+ASSERT from the
vlog compile line in run.do.
