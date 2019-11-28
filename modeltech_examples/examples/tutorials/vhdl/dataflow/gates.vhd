--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

--/////////////////////////////////////////////////
-- and2 cell:
--     Without the `celldefine compiler directive,
--     all internal primitives will be seen in the
--     dataflow window.
--/////////////////////////////////////////////////
library IEEE;
  use IEEE.std_logic_1164.all;
  USE ieee.vital_timing.ALL;
  USE ieee.vital_primitives.ALL;
entity and2 is
    GENERIC (
        TimingChecksOn : Boolean := True;
        InstancePath   : STRING := "*";
        Xon            : Boolean := True;
        MsgOn          : Boolean := False;
        -- path delays
        tpd_a_y       : VitalDelayType01 := (0.100 ns, 0.100 ns);
        tpd_b_y       : VitalDelayType01 := (0.100 ns, 0.100 ns);
        -- interconnect delays
        tipd_a        : VitalDelayType01 := (0.000 ns, 0.000 ns);
        tipd_b        : VitalDelayType01 := (0.000 ns, 0.000 ns)
    );
    port (a, b : IN  std_ulogic;
        y    : OUT std_ulogic );
    ATTRIBUTE vital_level0 OF and2 : ENTITY IS true;
end entity and2;

ARCHITECTURE vital_gate OF and2 IS

    ATTRIBUTE vital_level1 OF vital_gate : ARCHITECTURE IS true;
    SIGNAL a_ipd : std_ulogic := 'X';
    SIGNAL b_ipd : std_ulogic := 'X';

begin

    ------------------------------
    --  Wire Delays
    ------------------------------
    WireDelay : BLOCK
    BEGIN
        VitalWireDelay (a_ipd, a, tipd_a);
        VitalWireDelay (b_ipd, b, tipd_b);
    END BLOCK;

    ------------------------------
    --  Behavior section
    ------------------------------
    VITALBehavior : PROCESS (a_ipd, b_ipd)
        -- functionality results
        VARIABLE Results : std_logic_vector(1 TO 1) := (OTHERS => 'X');
        ALIAS y_zd : std_logic IS Results(1);
        -- output glitch detection variables
        VARIABLE y_GlitchData : VitalGlitchDataType;
    BEGIN
        ------------------------------
        --  Functionality Section
        ------------------------------
        y_zd := (a_ipd) AND (b_ipd);
        ------------------------------
        --  Path Delay Section
        ------------------------------
        VitalPathDelay01 (
            OutSignal     => y,
            GlitchData    => y_GlitchData,
            OutSignalName => "y",
            OutTemp       => y_zd,
            Paths         => (0 => (b_ipd'last_event, tpd_b_y, true),
                              1 => (a_ipd'last_event, tpd_a_y, true)),
            Mode          => OnEvent,
            Xon           => Xon,
            MsgOn         => MsgOn,
            MsgSeverity   => WARNING);
    END PROCESS;

END vital_gate;

--/////////////////////////////////////////////////
-- or2 cell:
--     This cell will be seen as a primitive since
--     it uses the `celldefine compiler directive.
--/////////////////////////////////////////////////
library IEEE;
  use IEEE.std_logic_1164.all;
  USE ieee.vital_timing.ALL;
  USE ieee.vital_primitives.ALL;
entity or2 is
    GENERIC (
        TimingChecksOn : Boolean := True;
        InstancePath   : STRING := "*";
        Xon            : Boolean := True;
        MsgOn          : Boolean := False;
        -- path delays
        tpd_a_y       : VitalDelayType01 := (0.100 ns, 0.100 ns);
        tpd_b_y       : VitalDelayType01 := (0.100 ns, 0.100 ns);
        -- interconnect delays
        tipd_a        : VitalDelayType01 := (0.000 ns, 0.000 ns);
        tipd_b        : VitalDelayType01 := (0.000 ns, 0.000 ns)
    );
    port (a, b : IN  std_ulogic;
        y    : OUT std_ulogic );
    ATTRIBUTE vital_level0 OF or2 : ENTITY IS true;
end entity or2;

ARCHITECTURE vital_gate OF or2 IS

    ATTRIBUTE vital_level1 OF vital_gate : ARCHITECTURE IS true;
    SIGNAL a_ipd : std_ulogic := 'X';
    SIGNAL b_ipd : std_ulogic := 'X';

begin

    ------------------------------
    --  Wire Delays
    ------------------------------
    WireDelay : BLOCK
    BEGIN
        VitalWireDelay (a_ipd, a, tipd_a);
        VitalWireDelay (b_ipd, b, tipd_b);
    END BLOCK;

    ------------------------------
    --  Behavior section
    ------------------------------
    VITALBehavior : PROCESS (a_ipd, b_ipd)
        -- functionality results
        VARIABLE Results : std_logic_vector(1 TO 1) := (OTHERS => 'X');
        ALIAS y_zd : std_logic IS Results(1);
        -- output glitch detection variables
        VARIABLE y_GlitchData : VitalGlitchDataType;
    BEGIN
        ------------------------------
        --  Functionality Section
        ------------------------------
        y_zd := (a_ipd) OR (b_ipd);
        ------------------------------
        --  Path Delay Section
        ------------------------------
        VitalPathDelay01 (
            OutSignal     => y,
            GlitchData    => y_GlitchData,
            OutSignalName => "y",
            OutTemp       => y_zd,
            Paths         => (0 => (b_ipd'last_event, tpd_b_y, true),
                              1 => (a_ipd'last_event, tpd_a_y, true)),
            Mode          => OnEvent,
            Xon           => Xon,
            MsgOn         => MsgOn,
            MsgSeverity   => WARNING);
    END PROCESS;

END vital_gate;
