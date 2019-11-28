library ieee;
USE ieee.std_logic_1164.all;

ENTITY bt4r IS
   PORT (
      a	: IN    std_logic;
      en	: IN    std_logic;
      tn	: IN    std_logic;
      Z	: OUT   std_logic
   );
END bt4r;

ARCHITECTURE bt4r_ARCH OF bt4r IS

BEGIN 
Z <= 'Z' WHEN (en = '1' OR tn = '0') ELSE a;
END bt4r_ARCH;

