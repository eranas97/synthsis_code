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


#ifndef PIPELINED_SLAVE_BASE_HEADER
#define PIPELINED_SLAVE_BASE_HEADER

#include "pipelined_protocol.h"
#include "bus_types.h"

using tlm::tlm_fifo;


class pipelined_slave : 
  public sc_module ,
  public virtual address_if , 
  public virtual data_if
{
public:

  pipelined_slave( sc_module_name module_name ,
		   int k = 10 ,
		   int d = 1 );

  sc_export<  address_if > address_export;
  sc_export< data_if > data_export;

  address_phase_status transport( const address_phase_request< ADDRESS_TYPE > &req );
  data_phase_response<DATA_TYPE> transport( const data_phase_request< DATA_TYPE > &req );

  ~pipelined_slave();

private:
  DATA_TYPE *memory;
  tlm_fifo< address_phase_request< ADDRESS_TYPE > > *pipeline;

};

#endif
