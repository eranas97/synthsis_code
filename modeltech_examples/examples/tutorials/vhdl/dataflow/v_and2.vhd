--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

------------------------------------------------------------------------------
LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.vital_timing.ALL;
USE ieee.vital_primitives.ALL;

ENTITY v_and2 IS
    GENERIC (
        TimingChecksOn : Boolean := True;
        InstancePath   : STRING := "*";
        Xon            : Boolean := True;
        MsgOn          : Boolean := False;
        -- path delays
        tpd_i1_y       : VitalDelayType01 := (0.100 ns, 0.100 ns);
        tpd_i0_y       : VitalDelayType01 := (0.100 ns, 0.100 ns);
        -- interconnect delays
        tipd_i1        : VitalDelayType01 := (0.000 ns, 0.000 ns);
        tipd_i0        : VitalDelayType01 := (0.000 ns, 0.000 ns)
    );
    PORT (
        y  : OUT std_ulogic;
        i1 : IN  std_ulogic;
        i0 : IN  std_ulogic
    );
    ATTRIBUTE vital_level0 OF v_and2 : ENTITY IS true;
END v_and2;

ARCHITECTURE vital_gate OF v_and2 IS

    ATTRIBUTE vital_level1 OF vital_gate : ARCHITECTURE IS true;
    SIGNAL i1_ipd : std_ulogic := 'X';
    SIGNAL i0_ipd : std_ulogic := 'X';

begin

    ------------------------------
    --  Wire Delays
    ------------------------------
    WireDelay : BLOCK
    BEGIN
        VitalWireDelay (i1_ipd, i1, tipd_i1);
        VitalWireDelay (i0_ipd, i0, tipd_i0);
    END BLOCK;

    ------------------------------
    --  Behavior section
    ------------------------------
    VITALBehavior : PROCESS (i1_ipd, i0_ipd)
        -- functionality results
        VARIABLE Results : std_logic_vector(1 TO 1) := (OTHERS => 'X');
        ALIAS y_zd : std_logic IS Results(1);
        -- output glitch detection variables
        VARIABLE y_GlitchData : VitalGlitchDataType;
    BEGIN
        ------------------------------
        --  Functionality Section
        ------------------------------
        y_zd := (i0_ipd) AND (i1_ipd);
        ------------------------------
        --  Path Delay Section
        ------------------------------
        VitalPathDelay01 (
            OutSignal     => y,
            GlitchData    => y_GlitchData,
            OutSignalName => "y",
            OutTemp       => y_zd,
            Paths         => (0 => (i1_ipd'last_event, tpd_i1_y, true),
                              1 => (i0_ipd'last_event, tpd_i0_y, true)),
            Mode          => OnEvent,
            Xon           => Xon,
            MsgOn         => MsgOn,
            MsgSeverity   => WARNING);
    END PROCESS;

END vital_gate;
