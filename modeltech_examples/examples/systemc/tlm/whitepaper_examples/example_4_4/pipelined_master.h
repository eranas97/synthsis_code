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


#ifndef PIPELINED_MASTER_HEADER
#define PIPELINED_MASTER_HEADER

#include "pipelined_protocol.h"
#include "bus_types.h"

using tlm::tlm_fifo;

class pipelined_master : 
  public sc_module
{
public:

  pipelined_master( sc_module_name module_name );

  sc_port< address_if > address_port;
  sc_port< data_if > data_port;

  SC_HAS_PROCESS( pipelined_master );

private:
  void address_phase();
  void data_phase();

  bool initiate_read( const ADDRESS_TYPE &a );
  bool initiate_write( const ADDRESS_TYPE &a , const DATA_TYPE &d ); 
  
  tlm_fifo< data_phase_request< DATA_TYPE > > outstanding;

};


#endif
