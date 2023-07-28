-- ROUND ROBBIN ARBITER MODULE
-- Date : 13.06.2023.
-- Creator : Aleksa Djokovic

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity arbiter_rr is
	port (
		clk: 		in std_logic;
		rstn: 	in std_logic;
		busy: in std_logic;
		
		-- inputs
		req:		in std_logic_vector;
		
		-- outputs
		gnt:		out std_logic_vector
	);
end arbiter_rr;

architecture rtl of arbiter_rr is

	signal double_req : unsigned(2*req'left+1 downto 0);
	signal double_gnt : unsigned(2*req'left+1 downto 0);
	signal priority : unsigned(req'left downto 0);
	signal last_req : std_logic_vector(req'left downto 0);
	
begin 

	double_req	<= unsigned(req & req);
	double_gnt  <= double_req and not (double_req-priority);	

	arbiter_pr: process (clk) 
		begin 
		if (rising_edge(clk)) then
		-- BUG Reset is not on 0 
		if (rstn = '1') then 
			priority(req'left downto 1) <= (others => '0');
			priority(0)	<= '1';
			last_req <= (others => '0');
			gnt	<= (others => '0');
		elsif (last_req /= req and busy /= '1') then
			priority(req'left downto 1) <= priority(req'left-1 downto 0);
			priority(0) <= priority(req'left);
			last_req <= req;
			gnt <= std_logic_vector(double_gnt(req'left downto 0) or double_gnt(2*req'left+1 downto req'left+1));
		end if;	
		end if;
	end process arbiter_pr;

end rtl;
