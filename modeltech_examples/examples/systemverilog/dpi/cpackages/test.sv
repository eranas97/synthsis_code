module top;
    import mti_fli::*;

    localparam int TCL_OK = 0;
    int A;
    int status;
    string s;
    chandle interp;

    initial begin : mti_Command_method
        //
        // Using mti_Command() is very simple.
        // However, you can not check error status.
        //
        #1;
        mti_Command("change A 42");
        $write("A is %0d at time %2d\n", A, $time);

        #1;
        s="change A 1999";
        mti_Command(s);
        $write("A is %0d at time %2d\n", A, $time);

        #1;
        s="force A 1234";
        mti_Command(s);
        $write("A is %0d at time %2d\n", A, $time);

        A = 5678;
        $write("A is %0d at time %2d\n", A, $time);

        mti_Command("noforce A");

        #1;
        mti_Command("change B 42");
    end

    initial begin : mti_Cmd_method
        #11;

        //
        // When using mti_Cmd(), you can check error status.
        // However, you must be sure to reset the Tcl interpreter
        // after each call you make to mti_Cmd().
        //
        interp = mti_Interp();

        if (mti_Cmd("change A 42") != TCL_OK)
            $write(Tcl_GetStringResult(interp));
        $write("A is %0d at time %2d\n", A, $time);
        Tcl_ResetResult(interp);

        #1;
        s="change A 1999";
        assert(mti_Cmd(s) == TCL_OK)
        else
            $error("%s", Tcl_GetStringResult(interp));
        $write("A is %0d at time %2d\n", A, $time);
        Tcl_ResetResult(interp);

        #1;
        s="force A 1234";
        assert(mti_Cmd(s) == TCL_OK)
        else
            $error("%s", Tcl_GetStringResult(interp));
        $write("A is %0d at time %2d\n", A, $time);
        Tcl_ResetResult(interp);

        A = 5678;
        $write("A is %0d at time %2d\n", A, $time);

        assert(mti_Cmd("noforce A") == TCL_OK)
        else
            $error("%s", Tcl_GetStringResult(interp));
        Tcl_ResetResult(interp);

        #1;
        assert(mti_Cmd("change B 42") == TCL_OK)
        else
            $error("%s", Tcl_GetStringResult(interp));
        Tcl_ResetResult(interp);

        #1;
        if (mti_Cmd("change B 42") != TCL_OK)
            $write(Tcl_GetStringResult(interp));
        Tcl_ResetResult(interp);

    end

endmodule
