
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity hamming_check is
    Port ( 
           data_in : in  std_logic_vector(7 downto 0);
           parity_in : in  std_logic_vector(3 downto 0);
           parity_check_out : out std_logic_vector(3 downto 0));
end hamming_check;

architecture Behavioral of hamming_check is
begin
    process(data_in, parity_in)
    begin
        -- calculate the parity bits
        parity_check_out(0) <= parity_in(0) xor data_in(0) xor data_in(1) xor data_in(3) xor data_in(4) xor data_in(6);
        parity_check_out(1) <= parity_in(1) xor data_in(0) xor data_in(2) xor data_in(3) xor data_in(5) xor data_in(6);
        parity_check_out(2) <= parity_in(2) xor data_in(1) xor data_in(2) xor data_in(3) xor data_in(7);
        parity_check_out(3) <= parity_in(3) xor data_in(4) xor data_in(5) xor data_in(6) xor data_in(7);

    end process;
end Behavioral;
