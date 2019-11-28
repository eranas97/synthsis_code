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


#include "master.h"
#include "mem_slave.h"

#include "sc_export.h"

using user::master;
using user::mem_slave;

class top : public sc_module
{
public:

  top( sc_module_name module_name ) :
    sc_module( module_name ) ,
    m("master") ,
    s("slave") {

      m.initiator_port( s.target_port );

  }

private:
  master m;
  mem_slave s;

};
 

#ifndef MTI_SYSTEMC
int sc_main( int argc , char **argv )
{

  top("top");
  sc_start( -1 );

  return 0;

}
#else
SC_MODULE_EXPORT(top);
#endif


