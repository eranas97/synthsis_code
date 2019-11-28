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


#ifndef MASTER_HEADER
#define MASTER_HEADER

#include <systemc.h>

#include "bus_types.h"
#include "basic_initiator_port.h"

using basic_protocol::basic_initiator_port;

namespace user
{

class switch_master : public sc_module
{
public:
  switch_master( sc_module_name module_name ,
		 bool p , DATA_TYPE s ,
		 ADDRESS_TYPE m = 0x20 );

  SC_HAS_PROCESS( switch_master );

  basic_initiator_port<ADDRESS_TYPE,DATA_TYPE> initiator_port;

private:
  void run();
  ADDRESS_TYPE start_address();

  bool parity;
  DATA_TYPE start_data;
  ADDRESS_TYPE max_address;

};

};

#endif
