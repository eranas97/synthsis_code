--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

library IEEE;
use IEEE.std_logic_1164.all;

package std_logic_util is
    function CONV_STD_LOGIC_VECTOR(ARG: INTEGER; SIZE: INTEGER) 
                               return STD_LOGIC_VECTOR;
    function CONV_INTEGER(ARG: STD_LOGIC_VECTOR) return INTEGER;
end std_logic_util;

package body std_logic_util is
    type tbl_type is array (STD_ULOGIC) of STD_ULOGIC;
    constant tbl_BINARY : tbl_type :=
             ('0', '0', '0', '1', '0', '0', '0', '1', '0');

    function CONV_STD_LOGIC_VECTOR(ARG: INTEGER; SIZE: INTEGER) 
                        return STD_LOGIC_VECTOR is
      variable result: STD_LOGIC_VECTOR(SIZE-1 downto 0);
      variable temp: integer;
    begin
      temp := ARG;
      for i in 0 to SIZE-1 loop
        if (temp mod 2) = 1 then
          result(i) := '1';
        else 
          result(i) := '0';
        end if;
        if temp > 0 then
          temp := temp / 2;
        else
          temp := (temp - 1) / 2; -- simulate ASR
        end if;
      end loop;
      return result;
    end;

    function CONV_INTEGER(ARG: STD_LOGIC_VECTOR) return INTEGER is
      variable result: INTEGER;
    begin
      assert ARG'length <= 32
        report "ARG is too large in CONV_INTEGER"
        severity FAILURE;
      result := 0;
      for i in ARG'range loop
        if i /= ARG'left then
          result := result * 2;
          if tbl_BINARY(ARG(i)) = '1' then
            result := result + 1;
          end if;
        end if;
      end loop;
      return result;
    end;
end std_logic_util;
