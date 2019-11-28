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


#ifndef MEM_SLAVE_HEADER
#define MEM_SLAVE_HEADER

#include "systemc.h"

#include "bus_types.h"
#include "basic_protocol.h"
#include "basic_slave_base.h"

using basic_protocol::basic_status;
using basic_protocol::basic_slave_base;
using tlm::tlm_transport_if;

namespace user
{

class mem_slave :
  public sc_module ,
  public virtual basic_slave_base< ADDRESS_TYPE , DATA_TYPE >
{
public:
  mem_slave( sc_module_name module_name , int k = 10 );

  sc_export< if_type > target_port;

  basic_status write( const ADDRESS_TYPE & , const DATA_TYPE & );
  basic_status read( const ADDRESS_TYPE & , DATA_TYPE & );

  ~mem_slave();

private:
  ADDRESS_TYPE *memory;

};

};

#endif
