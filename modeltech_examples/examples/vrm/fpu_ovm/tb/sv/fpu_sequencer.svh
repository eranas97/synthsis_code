// Not used in this example
class fpu_sequencer extends ovm_sequencer #(fpu_request, fpu_response);
`ovm_sequencer_utils(fpu_sequencer)

function new(string name, ovm_component parent=null);
      super.new(name, parent);
      `ovm_update_sequence_lib_and_item(fpu_request)
endfunction // new

endclass

