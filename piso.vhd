
library IEEE; 
use IEEE.STD_LOGIC_1164.ALL; 
use IEEE.NUMERIC_STD.ALL;

entity piso is 
port( 
        clk: in std_logic; 
        reset : in std_logic; --active high reset
        start_piso : in std_logic;
        -- shift : in std_logic;
        d : in std_logic_vector(31 downto 0);
        crc_stall : out std_logic;
        q : out std_logic;

        burst_len : in std_logic_vector(7 downto 0);
        vld_bytes_last_pulse_cnt : in std_logic_vector(1 downto 0)
        ); 
end piso; 


architecture Behavioral of piso is
  type state_t is (IDLE, LOAD, SHIFT, LAST_LOAD, LAST_SHIFT);
  signal state_reg, state_next : state_t;

  signal shift_s : std_logic;
  signal shift_cnt_max_reg, shift_cnt_max_next : std_logic_vector(4 downto 0);
  signal shift_cnt_reg, shift_cnt_next : std_logic_vector(4 downto 0);

  signal pulse_cnt_reg, pulse_cnt_next : std_logic_vector(7 downto 0);

  signal q_s : std_logic_vector(31 downto 0);
begin

  fsm_seq_proc: process(clk)
  begin
      if(clk'event and clk = '1') then
        if reset = '1' then
          state_reg <= IDLE;

          shift_cnt_max_reg <= (others => '0');
          pulse_cnt_reg <= (others => '0');
        else
          state_reg <= state_next;
          shift_cnt_max_next <= shift_cnt_max_reg;
          pulse_cnt_reg <= pulse_cnt_next;

        end if;
      end if;
  end process; 


  fsm_comb_proc:process(state_reg, pulse_cnt_reg, shift_cnt_max_reg, start_piso) is
  begin

    -- default values
    state_next <= state_reg;
    -- shift_cnt_max_next <= std_logic_vector(to_unsigned(31, 5));
    shift_cnt_max_next <= shift_cnt_max_reg;
    pulse_cnt_next <= pulse_cnt_reg;
    crc_stall <= '1';
    shift_s <= '0';

    case state_reg is
      when IDLE =>
        shift_cnt_max_next <= std_logic_vector(to_unsigned(31, 5));
        pulse_cnt_next <= (others => '0');

        if(start_piso = '1') then
          ---------------------------------------- 
          state_next <= LOAD;
          ---------------------------------------- 
        else
          ---------------------------------------- 
          state_next <= IDLE;
          ---------------------------------------- 
        end if;
      
      when LOAD =>
        -- load new pulse of 4 bytes 
        shift_s <= '0';
        -- crc_stall <= '1';
        pulse_cnt_next <= std_logic_vector(unsigned(pulse_cnt_reg) + 1);

        ---------------------------------------- 
        state_next <= SHIFT;
        ---------------------------------------- 
      when SHIFT =>
        shift_s <= '1';
        crc_stall <= '0';
        pulse_cnt_next <= std_logic_vector(unsigned(pulse_cnt_reg) + 1);

        if(unsigned(shift_cnt_reg) = unsigned(shift_cnt_max_reg)) then
          if(unsigned(pulse_cnt_reg) = unsigned(burst_len) - 1) then
            shift_cnt_max_next <= std_logic_vector(to_unsigned((to_integer((unsigned(vld_bytes_last_pulse_cnt)*8) + 7)), 5));
            ---------------------------------------- 
            state_next <= LAST_LOAD;
            ---------------------------------------- 
          else
            ---------------------------------------- 
            state_next <= LOAD;
            ---------------------------------------- 
          end if;
        else
          ---------------------------------------- 
          state_next <= SHIFT;
          ---------------------------------------- 
        end if;

        ---------------------------------------- 
        state_next <= SHIFT;
        ---------------------------------------- 
      when LAST_LOAD =>
        -- load new pulse of 4 bytes 
        shift_s <= '0';
        -- crc_stall <= '1';
        pulse_cnt_next <= std_logic_vector(unsigned(pulse_cnt_reg) + 1);

        ---------------------------------------- 
        state_next <= LAST_SHIFT;
        ---------------------------------------- 
      when LAST_SHIFT =>
        shift_s <= '1';
        crc_stall <= '0';
        pulse_cnt_next <= std_logic_vector(unsigned(pulse_cnt_reg) + 1);

        if(unsigned(shift_cnt_reg) = unsigned(shift_cnt_max_reg)) then
          ---------------------------------------- 
          state_next <= LAST_SHIFT;
          ---------------------------------------- 
        else
          ---------------------------------------- 
          state_next <= IDLE;
          ---------------------------------------- 
        end if;
    end case;
  end process;

  piso_reg: process (clk) is
  begin
    if (rising_edge(clk)) then
      if(reset = '1') then
        q_s <= (others => '0');
      else
        if (shift_s = '0') then
          q_s <= d;
        else
          q <= q_s(0);
          q_s <= '0'&q_s(31 downto 1);
        end if;
      end if;
    end if;
  end process;

end Behavioral;