This VPI routine defines the system task $mti_probe().  The system task has
the following syntax:

    $mti_probe(list_of_arguments);

The list of arguments can contain modules, nets, registers, or a character
identifier each separated by commas.  A dot separated path must be specified
for each reference to a module, net, or register that is not in the current
scope.  Each call to $mti_probe must contain at least one argument.  For
example:

    $mti_probe(top.dut);
    $mti_probe(clk);
    $mti_probe(top.dut.r0.rst, top, z_l);

The character identifier refers to a single or double character that
represents a certain logging behavior.  Below are the supported identifiers:

    "A"  Log all nodes in the current scope including nets, ports, etc.
    "AC" Recursively log all nodes starting in the current scope.
    "C"  Recursively log ONLY ports starting in the current scope.

Some other examples:

    $mti_probe("A");
    $mti_probe("AC", top.dut.z_l);
    $mti_probe(dut.r0.z_l, "C", z_l, top.dut);
