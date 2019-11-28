This example shows the following SystemVerilog features:

    * Classes
    * Dynamic arrays of class instances

This example demonstrates how to model a parameterized dynamic 2-dimensional
array of classes.  The package "DynPkg" contains declarations for several
classes.  The first class called "CELL" has several random variables and a
constraint on those variables.  The next class declaration "ROW" creates a
dynamic array of the first class "CELL".  The third class "FRAME" creates a
dynamic array of the class "ROW".  The "FRAME" class also includes a
parameterized constructor function for sizing the overall dimensions of the
array.

The important thing to note about calls to "new" in FRAME's "new" function is
that some are for initializing the dynamic arrays and others are for
constructing the class instances.  The first "new" method:

    R_Array = new[DEPTH];

creates a dynamic array of size "DEPTH" with each element of "R_Array" being
an object handle to a class instance of "ROW".  However at this point each of
these handles is set to NULL.

Since the elements of the dynamic arrays are "classes" they must be
constructed with "new" individually.  The first "for" loop is used to iterate
through each element in the "R_Array".  The first "new" method inside that
"for" loop constructs each instance of the "ROW" class.  The second "new"
method is called with "WIDTH" and created a dynamic array of "CELL" class
instances call "C_Array".

As with the "R_Array", each handle to the class instance needs to be
constructed.  Another "for" loop is used to iterate through each element of
"C_Array" and call the "new" method.

Finally, in the module "top", an instance of "FRAME" is created and the
constructor is passed the arguments (3,3) thus creating a 3x3 dynamic array
of the class "CELL".  The initial block in the top level module then simply
calls the built-in randomize function and prints out these random values.
