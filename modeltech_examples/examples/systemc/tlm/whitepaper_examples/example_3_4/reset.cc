/*****************************************************************************

  The following code is derived, directly or indirectly, from the SystemC
  source code Copyright (c) 1996-2004 by all Contributors.
  All Rights reserved.

  The contents of this file are subject to the restrictions and limitations
  set forth in the SystemC Open Source License Version 2.4 (the "License");
  You may not use this file except in compliance with such restrictions and
  limitations. You may obtain instructions on how to receive a copy of the
  License at http://www.systemc.org/. Software distributed by Contributors
  under the License is distributed on an "AS IS" basis, WITHOUT WARRANTY OF
  ANY KIND, either express or implied. See the License for the specific
  language governing rights and limitations under the License.

 *****************************************************************************/


#include "reset.h"

reset::reset( sc_module_name module_name , int reset_cycles ) :
  sc_module( module_name ) ,
  count( reset_cycles ) , max_count( reset_cycles ) {

  SC_METHOD( run );
  sensitive << clk.pos();
  
 
}

void reset::run() {

  if( count > 0 ) {

    rst = true;
    count--;

  }

  else {

    rst = false;

  }

}

