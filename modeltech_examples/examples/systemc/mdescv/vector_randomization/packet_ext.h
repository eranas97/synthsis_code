/* Model Technology ModelSim SE sccom DEV compiler 2003.05 Jun 24 2008 */

#ifndef MTI_type_H
#define MTI_type_H

#include "systemc.h"
#include "scv.h"
#include "packet.h"

SCV_EXTENSIONS(frame_t) {
	public:
		scv_extensions<sc_uint<32> > dest_addr;
		scv_extensions<sc_uint<32> > src_addr;
		scv_extensions<sc_uint<24> > tag;
		scv_extensions<sc_uint<8> > type;
		scv_extensions<sc_uint<64> > data;
		scv_extensions<sc_uint<32> > crc;

		SCV_EXTENSIONS_CTOR(frame_t) {
			SCV_FIELD(dest_addr);
			SCV_FIELD(src_addr);
			SCV_FIELD(tag);
			SCV_FIELD(type);
			SCV_FIELD(data);
			SCV_FIELD(crc);
		}
};

SCV_EXTENSIONS(packet_t) {
	public:
		scv_extensions<frame_t> frame;
		scv_extensions<sc_uint<16> > msg_length;
		scv_extensions<char[16]> msg;

		SCV_EXTENSIONS_CTOR(packet_t) {
			SCV_FIELD(frame);
			SCV_FIELD(msg_length);
			SCV_FIELD(msg);
		}
};

#endif
