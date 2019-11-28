// $Id: //dvt/mti/rel/6.4c/src/misc/examples/vlog_dut/test_status.sv#1 $
//----------------------------------------------------------------------
//   Copyright 2005 Mentor Graphics Corporation
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

//----------------------------------------------------------------------
// CLASS analysis_fifo
//
// Global indication of test status: any component can call
// a function to fail a test.  We also provide methods to
// report the status to the transcript.
//----------------------------------------------------------------------



// If an error is detected, should we fail immediately, or
// at the end of the test?  For regressions, you might as
// well fail immediately.  For development, it may be more
// useful to continue with the test and fail only at the
// end.
typedef enum { FAIL_IMMEDIATELY, FAIL_AT_END }  fail_mode_t;

bit             pass = 1'b1;
fail_mode_t     fail_mode;

// List of components who failed the test.
//string  failers[string];

    task set_fail_mode(fail_mode_t how);
        fail_mode = how;
    endtask
/*
    function void fail(string source, string more_info);
        failers[source] = more_info;
        pass = 1'b0;
        if (fail_mode == FAIL_IMMEDIATELY) report_status();
    endfunction
*/
    // Report status
    function automatic void report_status;
        string  i;

        if (pass) begin
            $display("*****************************************************");
            $display("*      #                                            *");
            $display("*     #                                             *");
            $display("*    #            T E S T   P A S S E D             *");
            $display("* # #                                               *");
            $display("*  #                                                *");
            $display("*****************************************************");
        end else begin
            $display("*****************************************************");
            $display("* #   #                                             *");
            $display("*  # #                                              *");
            $display("*   #             T E S T   F A I L E D             *");
            $display("*  # #                                              *");
            $display("* #   #                                             *");
            $display("*****************************************************");
            $display(" Individual failure points recorded by:");
/*            if (failers.first(i)) begin
                do begin
                    $display("  %s: %s", i, failers[i]);
                end while (failers.next(i));
            end*/
        end

       // $finish;
    endfunction
