This example shows the following SystemVerilog features:

    * Classes
    * Associative arrays of class instances

This example shows how handles to class objects work.  The example has an
associative array of class objects with the index to the array being a string.
When a new class instance is assigned to the array, what is really stored in
the array is a handle to the class object (a pointer in C terms).

Executing the run.do script will run two simulation.  The first simulation
will run without calling the "new" class method between each array assignment.
In this run you will notice that the value of each element in the array is the
same even though three different values have been assigned.  This is correct
behavior as all three elements of the array hold the same handle to the class
instance.  The values you get, are the current values in the class.

The second run actually calls the "new" class method between each assignment
to the array.  By doing this, you create new handles.  Each element in the
array is a different handle and represents the values in the class instance at
that specific time.  Notice the results of this run.  They are the three
different values that were assigned.
