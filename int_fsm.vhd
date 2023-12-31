library ieee;
use ieee.std_logic_1164.all;
use IEEE.NUMERIC_STD.ALL;

entity int_fsm is
    port (
        clk : in std_logic;
        reset : in std_logic;

        awvalid : in std_logic;
        bvalid : in std_logic;
        bready : in std_logic;

        arvalid : in std_logic;
        rlast : in std_logic;
        rvalid : in std_logic;
        rready : in std_logic;
        arlen : in std_logic_vector(7 downto 0);

        busy : out std_logic
    );
end entity int_fsm;

architecture Behavioral of int_fsm is

    type state_t is (AVAILABLE, BUSY_READ, BUSY_WRITE);

    signal state_reg, state_next : state_t;
    signal busy_internal : std_logic;

begin
  state: process(clk, reset)
  begin
      if reset = '1' then
          state_reg <= AVAILABLE;
      elsif(clk'event and clk = '1') then
          state_reg <= state_next;
      end if;
  end process; 

  process (state_reg, state_next, awvalid, bvalid, bready, arvalid, rlast)
  begin

    state_next <= state_reg;
    case state_reg is
      when AVAILABLE =>
        busy_internal <= '0';
        
        if arvalid = '1' then
          state_next <= BUSY_READ;  -- Transition to BUSY_READ state_next for read request
          busy_internal <= '1';
        elsif awvalid = '1' then
          state_next <= BUSY_WRITE;  -- Transition to BUSY_WRITE state_next for write request
          busy_internal <= '1';
        end if;
          
      when BUSY_READ =>
        busy_internal <= '1';
        
        -- FIX add handshake
        -- FIX consider single burst transaction
        if (rlast = '1' and rvalid = '1' and rready = '1') or (unsigned(arlen) = 0 and rvalid = '1' and rready = '1') then
          state_next <= AVAILABLE;  -- Transition back to AVAILABLE after read completion
	  busy_internal <= '0';
        end if;
          
      when BUSY_WRITE =>
        busy_internal <= '1';
        
        if bvalid = '1' and bready = '1' then
          state_next <= AVAILABLE;  -- Transition back to AVAILABLE after write completion
	  busy_internal <= '0';
        end if;
            
    end case;
  end process;
    
    busy <= busy_internal;
end architecture Behavioral;
