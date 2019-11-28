module a;
  parameter delay = 0;
  int a;
  initial begin
    #delay a = 1;
    assert (a == 0)
    else if ($test$plusargs("warning")) begin
      $warning("Assert warning from scope %m at time %0t", $time);
    end
    assert ((delay % 2) != 1)
    else if ($test$plusargs("warning")) begin
      $warning("Delay %0t is odd", $time);
    end
    assert ((delay % 3) != 1)
    else if ($test$plusargs("error")) begin
      $error("Bad xfer code on port FRED at time %0t", $time);
    end
    assert ((delay % 3) != 2)
    else if ($test$plusargs("error")) begin
      $error("Bad xfer code on port BOB at time %0t", $time);
    end
    assert ((delay % 5) != 1)
    else begin
      $info("Scope %m is monitoring port FRED");
      if ($test$plusargs("warning")) begin
        $warning("Out of bounds write on port FRED at time %0t", $time);
      end
    end
    assert ((delay % 5) != 2)
    else begin
      $info("Scope %m is monitoring port BOB");
      if ($test$plusargs("warning")) begin
        $warning("Out of bounds write on port BOB at time %0t", $time);
      end
    end
    assert (delay % 10)
    else begin
      $info("All is well at time %0t", $time);
    end
  end
endmodule
module top;
  a #(1) u1();
  a #(2) u2();
  a #(3) u3();
  a #(4) u4();
  a #(5) u5();
  a #(6) u6();
  a #(7) u7();
  a #(8) u8();
  a #(9) u9();
  a #(10) u10();
  a #(11) u11();
  a #(12) u12();
  a #(13) u13();
  a #(14) u14();
  a #(15) u15();
  a #(16) u16();
  a #(17) u17();
  a #(18) u18();
  a #(19) u19();
  a #(20) u20();
  a #(21) u21();
  a #(22) u22();
  a #(23) u23();
  a #(24) u24();
  a #(25) u25();
  a #(26) u26();
  a #(27) u27();
  a #(28) u28();
  a #(29) u29();
  a #(30) u30();
  a #(31) u31();
  a #(32) u32();
  a #(33) u33();
  a #(34) u34();
  a #(35) u35();
  a #(36) u36();
  a #(37) u37();
  a #(38) u38();
  a #(39) u39();
  a #(40) u40();
  a #(41) u41();
  a #(42) u42();
  a #(43) u43();
  a #(44) u44();
  a #(45) u45();
  a #(46) u46();
  a #(47) u47();
  a #(48) u48();
  a #(49) u49();
  a #(50) u50();
  a #(51) u51();
  a #(52) u52();
  a #(53) u53();
  a #(54) u54();
  a #(55) u55();
  a #(56) u56();
  a #(57) u57();
  a #(58) u58();
  a #(59) u59();
  a #(60) u60();
  a #(61) u61();
  a #(62) u62();
  a #(63) u63();
  a #(64) u64();
  a #(65) u65();
  a #(66) u66();
  a #(67) u67();
  a #(68) u68();
  a #(69) u69();
  a #(70) u70();
  a #(71) u71();
  a #(72) u72();
  a #(73) u73();
  a #(74) u74();
  a #(75) u75();
  a #(76) u76();
  a #(77) u77();
  a #(78) u78();
  a #(79) u79();
  a #(80) u80();
  a #(81) u81();
  a #(82) u82();
  a #(83) u83();
  a #(84) u84();
  a #(85) u85();
  a #(86) u86();
  a #(87) u87();
  a #(88) u88();
  a #(89) u89();
  a #(90) u90();
  a #(91) u91();
  a #(92) u92();
  a #(93) u93();
  a #(94) u94();
  a #(95) u95();
  a #(96) u96();
  a #(97) u97();
  a #(98) u98();
  a #(99) u99();
  a #(100) u100();
  initial begin
    assert (0)
    else begin
      $info("Loading initial microcode image");
      if ($test$plusargs("warning")) begin
        $warning("Waning moon could cause packet collisions");
      end
    end
  end
endmodule
