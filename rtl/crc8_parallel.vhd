-- CRC polynomial coefficients: x^8 + x^2 + x + 1
--                              0x7 (hex)
-- CRC width:                   8 bits
-- CRC shift direction:         left (big endian)
-- Input word width:            8 bits

library IEEE;
use IEEE.std_logic_1164.all;

entity crc8 is
    port (
        crc_in: in std_logic_vector(7 downto 0);
        data_in: in std_logic_vector(7 downto 0);
        crc_out: out std_logic_vector(7 downto 0)
    );
end entity crc8;

architecture Behavioral of crc8 is
begin
    crc_out(0) <= crc_in(0) xor crc_in(6) xor crc_in(7) xor data_in(0) xor data_in(6) xor data_in(7);
    crc_out(1) <= crc_in(0) xor crc_in(1) xor crc_in(6) xor data_in(0) xor data_in(1) xor data_in(6);
    crc_out(2) <= crc_in(0) xor crc_in(1) xor crc_in(2) xor crc_in(6) xor data_in(0) xor data_in(1) xor data_in(2) xor data_in(6);
    crc_out(3) <= crc_in(1) xor crc_in(2) xor crc_in(3) xor crc_in(7) xor data_in(1) xor data_in(2) xor data_in(3) xor data_in(7);
    crc_out(4) <= crc_in(2) xor crc_in(3) xor crc_in(4) xor data_in(2) xor data_in(3) xor data_in(4);
    crc_out(5) <= crc_in(3) xor crc_in(4) xor crc_in(5) xor data_in(3) xor data_in(4) xor data_in(5);
    crc_out(6) <= crc_in(4) xor crc_in(5) xor crc_in(6) xor data_in(4) xor data_in(5) xor data_in(6);
    crc_out(7) <= crc_in(5) xor crc_in(6) xor crc_in(7) xor data_in(5) xor data_in(6) xor data_in(7);
end architecture Behavioral;