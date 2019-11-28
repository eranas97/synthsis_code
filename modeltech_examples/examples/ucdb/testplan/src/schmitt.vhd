library ieee;
USE ieee.std_logic_1164.all;

ENTITY schmitt IS
   PORT (
      a	: IN    std_logic;
      pi	: IN    std_logic;
      Z	: OUT   std_logic;
      po	: OUT   
   std_logic
   );
END schmitt;

ARCHITECTURE schmitt_ARCH OF schmitt IS
BEGIN

Z <= a;
po <= NOT (a AND pi);

END schmitt_ARCH;
