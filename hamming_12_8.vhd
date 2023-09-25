library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity hamming_12_8 is
    Port ( 
           data_in : in  STD_LOGIC_VECTOR(7 downto 0);
           parity_out : out  STD_LOGIC_VECTOR(3 downto 0));
end hamming_12_8;

architecture Behavioral of hamming_12_8 is
begin
    process(data_in)
    begin
        -- calculate the parity bits
        parity_out(0) <= data_in(0) xor data_in(1) xor data_in(3) xor data_in(4) xor data_in(6);
        parity_out(1) <= data_in(0) xor data_in(2) xor data_in(3) xor data_in(5) xor data_in(6);
        parity_out(2) <= data_in(1) xor data_in(2) xor data_in(3) xor data_in(7);
        parity_out(3) <= data_in(4) xor data_in(5) xor data_in(6) xor data_in(7);
    end process;
end Behavioral;
