
OSCI SystemC TLM Standard
17 November 2004

This kit contains the proposed OSCI SystemC TLM
standard API, documentation, and examples.

For introductory presentations, see docs/intro_tlm.pdf 
and docs/tlm_whitepaper.pdf

This kit works with both SystemC 2.0.1 and
SystemC 2.1, both available from www.systemc.org.
However SystemC 2.1 is recommended since it natively
supports sc_export, and because there
are a few relatively minor TLM features that cannot be supported
on SystemC 2.0.1. This kit has been tested on most or
all of the supported compilers and platforms that comprise
the supported compilers and platforms for OSCI SystemC 2.0.1
and 2.1 releases. However this kit has not yet been
tested on the Microsoft Visual C++ compiler.

There is no build procedure needed for the TLM library,
since the entire library is in '.h' files.

The 'tlm' directory contains the interfaces and
code that comprise the proposed OSCI SystemC TLM
standard. Files that are outside of the 'tlm' directory
are not considered to be part of the official standard,
but are instead considered examples and documentation.

All examples described in the tlm_whitepaper are
included in the whitepaper_examples directory.

There are make files included with each of the 
examples in the whitepapar_examples directory.

See also the README files in several of the directories
in this kit.

