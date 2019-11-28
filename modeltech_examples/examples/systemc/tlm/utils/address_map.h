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


#ifndef ADDRESS_MAP_HEADER
#define ADDRESS_MAP_HEADER

#include <map>
#include <string>

//
// address_map is a 1-1 mapping from port id to address_range.
// 
// The decode function tells us which, if any, adddress range we're in
// if we're in one, it adjusts the address and returns the port index
//
// The new address and port index are used to route the request to 
// the appropriate slave.
//
// address_range is mainly internal but you can use it externally if you want
//

using std::map;
using std::string;

namespace utils
{

template< class ADDRESS >
class address_range
{
public:
  ADDRESS from , to;

  address_range( const ADDRESS &l , const ADDRESS &h ) : from( l ) , to( h ) {}

  address_range ( const address_range<ADDRESS> &a ) {

    from = a.from;
    to = a.to;

  }

  address_range () : from( 0 ) , to( 0 ) {}
 
  bool decode( const ADDRESS &before , ADDRESS &after ) const {

    if( from <= before && before < to ) {
      after = before - from;
      return true;
    }

    return false;

  }

};

template< class ADDRESS >
class address_map
{
public:

  bool decode( const ADDRESS &before , ADDRESS &after , int &p ) const;

  void add_to_map( const ADDRESS &from , const ADDRESS &to , int p ) {

    address_range_map[p] = address_range<ADDRESS>( from , to ) ;

  }

private:
  map< int , address_range<ADDRESS> > address_range_map;

};

template<typename ADDRESS>
bool address_map<ADDRESS>::decode( const ADDRESS &before , ADDRESS &after , int &p ) const
{

  typename map< int , address_range<ADDRESS> >::const_iterator i;

  for( i = address_range_map.begin();
       i != address_range_map.end();
       ++i ) {
      
    if( (*i).second.decode( before , after ) ) {
	
      p = (*i).first;
      return true;

    }

  }

  return false;

}

};

#endif
