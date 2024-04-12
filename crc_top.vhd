library IEEE; 
use IEEE.STD_LOGIC_1164.ALL; 
use IEEE.NUMERIC_STD.ALL;

entity crc_top is 
port( 
        clk: in std_logic; 
        reset : in std_logic; --active high reset
        
        start_crc : in std_logic;
        pulse_cnt_max : in std_logic_vector(1 downto 0);
				-- for every data sel
        vld_bytes_last_pulse_cnt : in std_logic_vector(1 downto 0);
        data_sel : in std_logic_vector(3 downto 0);

        data_in : in std_logic_vector(31 downto 0);
        data_req: out std_logic;
        crc_out : out std_logic_vector(7 downto 0);
        crc_ready : out std_logic
        ); 
end crc_top; 


architecture Behavioral of crc_top is

  component crc8 is
      port (
          crc_in: in std_logic_vector(7 downto 0);
          data_in: in std_logic_vector(7 downto 0);
          crc_out: out std_logic_vector(7 downto 0)
      );
  end component crc8;

  type state_t is (IDLE, LOAD, SHIFT, LAST_LOAD, LAST_SHIFT);
  signal state_reg, state_next : state_t;

  -- shift reg signals
  signal shift_s : std_logic;
  signal shift_cnt_reg, shift_cnt_next : std_logic_vector(4 downto 0);
  signal pulse_cnt_reg, pulse_cnt_next : std_logic_vector(1 downto 0);
  signal crc_ready_reg, crc_ready_next : std_logic;

  -- crc signals
  signal crc_reg : std_logic_vector(7 downto 0);
  signal crc_out_s : std_logic_vector(7 downto 0);

  signal q_s : std_logic_vector(31 downto 0);
begin

  -- output crc8
  crc_out <= crc_reg;
	crc_ready <= crc_ready_reg;

  -- crc mid result register
  crc_mid_res_reg: process(clk) is
  begin
    if (rising_edge(clk)) then
      if(reset = '1') then
        crc_reg <= (others => '0');
			elsif(start_crc = '1') then
        crc_reg <= (others => '0');
      elsif(shift_s = '1') then
        crc_reg <= crc_out_s;
			else 
				crc_reg <= crc_reg;
      end if;
    end if;
  end process;

  -- shift register
  shift_reg: process (clk) is
  begin
    if (rising_edge(clk)) then
      if(reset = '1') then
        q_s <= (others => '0');
				-- COI removal
      else
        if (shift_s = '0') then
          q_s <= data_in;
        else
          q_s <= std_logic_vector(to_unsigned(0, 8))&q_s(31 downto 8);
        end if;
      end if;
    end if;
  end process;

  fsm_seq_proc: process(clk)
  begin
      if(clk'event and clk = '1') then
        if reset = '1' then
          state_reg <= IDLE;
          shift_cnt_reg <= (others => '0');
          pulse_cnt_reg <= (others => '0');
          crc_ready_reg <= '0';
        else
          state_reg <= state_next;
          shift_cnt_reg <= shift_cnt_next;
          pulse_cnt_reg <= pulse_cnt_next;
					crc_ready_reg <= crc_ready_next;

        end if;
      end if;
  end process; 

  fsm_comb_proc:process(state_reg, pulse_cnt_reg, shift_cnt_reg, start_crc, data_in,
                        crc_ready_reg, crc_ready_next, pulse_cnt_max, vld_bytes_last_pulse_cnt) is
  begin

    -- default values
		-- COI removal
    -- state_next <= state_reg;
    pulse_cnt_next <= pulse_cnt_reg;
    shift_cnt_next <= shift_cnt_reg;
    shift_s <= '0';
    data_req <= '0';
    crc_ready_next <= '0';

    case state_reg is
      when IDLE =>
        -- shift_cnt_max_next <= std_logic_vector(to_unsigned(31, 5));
        pulse_cnt_next <= (others => '0');
				shift_cnt_next <= (others => '0');

        if(start_crc = '1') then
          if(to_integer(unsigned(pulse_cnt_max)) > 0) then
            ---------------------------------------- 
            state_next <= LOAD;
            ---------------------------------------- 
          else
            ---------------------------------------- 
            state_next <= LAST_LOAD;
            ---------------------------------------- 
          end if;
        else
          ---------------------------------------- 
          state_next <= IDLE;
          ---------------------------------------- 
        end if;
      
      when LOAD =>
        -- load new pulse of 4 bytes 
        shift_s <= '0';
        -- prepare data for next shift cycle
        data_req <= '1';

        pulse_cnt_next <= std_logic_vector(unsigned(pulse_cnt_reg) + 1);
        ---------------------------------------- 
        state_next <= SHIFT;
        ---------------------------------------- 
      when SHIFT =>

				shift_s <= '1';
				--BUG crc calculation implemented only for op2
				-- data sel case to be implemented, crc calc for op0 and op1
				case data_sel is 
					when x"0" =>
						-- no icrement of shift_cnt_reg because only lsb byte is used for crc calc, so load every cycle
						if(unsigned(pulse_cnt_reg) = unsigned(pulse_cnt_max)) then
							shift_cnt_next <= (others => '0');
							---------------------------------------- 
							state_next <= LAST_LOAD;
							---------------------------------------- 
						else
							shift_cnt_next <= (others => '0');
							---------------------------------------- 
							state_next <= LOAD;
							---------------------------------------- 
						end if;
					when x"1" =>
						if(to_integer(unsigned(shift_cnt_reg)) = 1) then
							if(unsigned(pulse_cnt_reg) = unsigned(pulse_cnt_max)) then
								shift_cnt_next <= (others => '0');
								---------------------------------------- 
								state_next <= LAST_LOAD;
								---------------------------------------- 
							else
								shift_cnt_next <= (others => '0');
								---------------------------------------- 
								state_next <= LOAD;
								---------------------------------------- 
							end if;
						else
							shift_cnt_next <= std_logic_vector(unsigned(shift_cnt_reg) + 1);
							---------------------------------------- 
							state_next <= SHIFT;
							---------------------------------------- 
						end if;
					when others =>
						if(to_integer(unsigned(shift_cnt_reg)) = 3) then
							if(unsigned(pulse_cnt_reg) = unsigned(pulse_cnt_max)) then
								shift_cnt_next <= (others => '0');
								---------------------------------------- 
								state_next <= LAST_LOAD;
								---------------------------------------- 
							else
								shift_cnt_next <= (others => '0');
								---------------------------------------- 
								state_next <= LOAD;
								---------------------------------------- 
							end if;
						else
							shift_cnt_next <= std_logic_vector(unsigned(shift_cnt_reg) + 1);
							---------------------------------------- 
							state_next <= SHIFT;
							---------------------------------------- 
						end if;
				end case;
					
      when LAST_LOAD =>
        -- load new pulse of 4 bytes 
        shift_s <= '0';

        ---------------------------------------- 
        state_next <= LAST_SHIFT;
        ---------------------------------------- 
      when LAST_SHIFT =>
        shift_s <= '1';
        shift_cnt_next <= std_logic_vector(unsigned(shift_cnt_reg) + 1);

        if(unsigned(shift_cnt_reg) = unsigned(vld_bytes_last_pulse_cnt)) then
          -- KEY signal crc calculation done
          crc_ready_next <= '1'; 
          ---------------------------------------- 
          state_next <= IDLE;
          ---------------------------------------- 
        else
          ---------------------------------------- 
          state_next <= LAST_SHIFT;
          ---------------------------------------- 
        end if;
    end case;
  end process;

  -- crc calculator
  crc_calc: crc8
  port map(
    crc_in => crc_reg, 
		-- crc_data_in_s is register which makes 1 cycle latency crc calc bug
		-- forward directly value from shift register 
    data_in => q_s(7 downto 0),
    crc_out => crc_out_s
  );


end Behavioral;
