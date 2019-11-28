--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

-- Description : RTL Configuration

configuration Test_Bench_RTL of test_ringbuf is
  for test_ringbuf_ARCH
    for ring_INST: ringbuf
      use entity work.ringbuf(RTL) ;
    end for ;
  end for;
end Test_Bench_RTL;
