package fpu_pkg;

import ovm_pkg::*;

import fpu_agent_pkg::*;

// scoreboard stuff
`include "ovm_macros.svh";
`include "fpu_macros.svh";

`include "fpu_comparator.svh"; // remove use OVM world reporting trix
`include "fpu_reference_model.svh";
`include "fpu_scoreboard.svh";
`include "fpu_environment.svh";

`include "fpu_test_base.svh";

`include "fpu_test_sequence_fair.svh";
`include "fpu_test_random_sequence.svh";
`include "fpu_test_neg_sqr_sequence.svh";
`include "fpu_test_simple_sanity.svh";
`include "fpu_test_patternset.svh";

endpackage // fpu_pkg
