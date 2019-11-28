module top;

// This example is showing how to make a DPI import call to allocate a SV dynamic
// array and initialize the elements with C data

int dynarr[];

// create a SV dynamic array using DPI import
import "DPI-C" context function void create_sv_dynarray();

// Fetch C data and initialize the SV dynamic array elements with C data.
import "DPI-C" context function void fetch_sv_dynarray_data_from_C(chandle cdata, inout int o []);

// Export call is to allocate a SV dynamic array as requested from C side
export "DPI-C" function alloc_sv_dynarray;


function void alloc_sv_dynarray(input int size, input chandle cdata);
      $display("new dynamic array size = %d", size);
      dynarr = new[size];
      fetch_sv_dynarray_data_from_C(cdata, dynarr);    
endfunction   

initial begin
   create_sv_dynarray();

   foreach (dynarr[i]) begin
      $display("dynarr[%0d] = %0d",i, dynarr[i]); 
   end

end
endmodule
