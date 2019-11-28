This example shows the following SystemVerilog features:

    * Basic interface usage
    * Interface modports
    * Tasks & functions in interfaces

The design uses the interface to model a popular verification element called
a Mailbox.  Mailboxes are typically used as a communication channel between
different processes.

SystemVerilog has a build-in Mailbox class and this Mailbox interface is
intended to be an example of how Mailboxes can be modeled by other methods.
It uses the same methods and calling conventions as the built-in class.  The
only major differences are:

    1) This interface example of a mailbox must be statically declared.

    2) There is no fairness if multiple threads are blocked while waiting onD
       a get or put.

The test for this interface example shows two different mailbox approaches:

    port1: Uses a normal data type, with the mailbox instantiated inside the
           test.

    port2: Uses an interface as the mailbox itself.
