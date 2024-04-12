
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
 
entity fifo is
  generic (
    DATA_WIDTH : natural := 32;
    FIFO_DEPTH : integer := 19
    );
  port (
    reset : in std_logic;
    clk      : in std_logic;
 
    -- FIFO Write Interface
    wr_en_i   : in  std_logic;
    wr_data_i : in  std_logic_vector(DATA_WIDTH-1 downto 0);
 
    -- FIFO Read Interface
    rd_pt_rst : in std_logic;
    rd_en_i   : in  std_logic;
    rd_data_o : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end fifo;
 
architecture rtl of fifo is
 
  type t_FIFO_DATA is array (0 to FIFO_DEPTH-1) of std_logic_vector(DATA_WIDTH-1 downto 0);
  signal fifo_data_s : t_FIFO_DATA;
  signal write_index_s   : std_logic_vector(4 downto 0);
  signal read_index_s   : std_logic_vector(4 downto 0);
begin
 
  p_CONTROL : process (clk) is
  begin
    if rising_edge(clk) then
      if reset = '1' then
        write_index_s   <= (others => '0');
        read_index_s   <= (others => '0');
  			fifo_data_s <= (others => (others => '0'));
      elsif(rd_pt_rst = '1') then
        read_index_s   <= (others => '0');
      else

        -- Keeps track of the write index (and controls roll-over)
        if (wr_en_i = '1') then
          if to_integer(unsigned(write_index_s)) = FIFO_DEPTH-1 then
						write_index_s   <= (others => '0');
          else
            write_index_s <= std_logic_vector(unsigned(write_index_s) + 1);
          end if;
        end if;

        -- Keeps track of the read index (and controls roll-over)        
        if (rd_en_i = '1') then
          if to_integer(unsigned(read_index_s)) = FIFO_DEPTH-1 then
						read_index_s   <= (others => '0');
          else
            read_index_s <= std_logic_vector(unsigned(read_index_s) + 1);
          end if;
        end if;

        -- Registers the input data when there is a write
        if wr_en_i = '1' then
          fifo_data_s(to_integer(unsigned(write_index_s))) <= wr_data_i;
        end if;
      end if;                           
    end if;                            
  end process p_CONTROL;
   
	-- async
  rd_data_o <= fifo_data_s(to_integer(unsigned(read_index_s)));

end rtl;
