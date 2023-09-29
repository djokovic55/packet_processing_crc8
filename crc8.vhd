library IEEE; 
use IEEE.STD_LOGIC_1164.ALL; 
use IEEE.NUMERIC_STD.ALL;

entity crc8 is 
port( 
        clk: in std_logic; 
        reset : in std_logic; --active high reset
        crc_stall : in std_logic;
        size_data : in std_logic_vector(15 downto 0);  --the size of input stream in bits.
        data_in : in std_logic; --serial input
        crc_out : out std_logic_vector(7 downto 0); --8 bit crc checksum
        crc_ready : out std_logic --high when the calculation is done.
        ); 
end crc8; 

architecture Behavioral of crc8 is 

signal count : unsigned(15 downto 0) := (others => '0');
signal crc_temp : unsigned(7 downto 0) := (others => '0');

begin
-- FIXME synq reset, simplier crc_stall flag check

process(clk,reset)
begin
    if(rising_edge(clk)) then
        if(reset = '1') then
            crc_temp <= (others => '0');
            count <= (others => '0');
            crc_ready <= '0';
        elsif(crc_stall /= '1') then
        -- IMPORTANT everything should stay stable if stall is active
        --     -- wait until data_in is prepared
        --     crc_temp <= crc_temp;
        -- else
        -- crc calculation in the next four lines.
        crc_temp(0) <= data_in xor crc_temp(7);
        crc_temp(1) <= crc_temp(0) xor crc_temp(7);
        crc_temp(2) <= crc_temp(1) xor crc_temp(7);
        crc_temp(7 downto 3) <= crc_temp(6 downto 2);
        
        count <= count + 1; --keeps track of the number of rounds
        if(unsigned(count) = unsigned(size_data) + 7) then --check when to finish the calculations
            count <= (others => '0');
            crc_ready <= '1';
        end if; 
        end if;
    end if; 
end process;    

crc_out <= std_logic_vector(crc_temp);

end Behavioral;