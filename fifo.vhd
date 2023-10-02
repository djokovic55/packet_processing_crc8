
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
    full_o    : out std_logic;
 
    -- FIFO Read Interface
    rd_pt_rst : in std_logic;
    rd_en_i   : in  std_logic;
    rd_data_o : out std_logic_vector(DATA_WIDTH-1 downto 0);
    empty_o   : out std_logic
    );
end fifo;
 
architecture rtl of fifo is
 
  type t_FIFO_DATA is array (0 to FIFO_DEPTH-1) of std_logic_vector(DATA_WIDTH-1 downto 0);
  signal fifo_data_s : t_FIFO_DATA := (others => (others => '0'));
 
  signal write_index_s   : integer range 0 to FIFO_DEPTH-1 := 0;
  signal read_index_s   : integer range 0 to FIFO_DEPTH-1 := 0;
 
  signal fifo_cnt_s : integer range 0 to FIFO_DEPTH := 0;
 
  signal full_s  : std_logic;
  signal empty_s : std_logic;
   
begin
 
  p_CONTROL : process (clk) is
  begin
    if rising_edge(clk) then
      if reset = '1' then
        fifo_cnt_s <= 0;
        write_index_s   <= 0;
        read_index_s   <= 0;
      elsif(rd_pt_rst = '1') then
        read_index_s <= 0;
      else
 
        -- Keeps track of the total number of words in the FIFO
        if (wr_en_i = '1' and rd_en_i = '0') then
          fifo_cnt_s <= fifo_cnt_s + 1;
        elsif (wr_en_i = '0' and rd_en_i = '1') then
          fifo_cnt_s <= fifo_cnt_s - 1;
        end if;
 
        -- Keeps track of the write index (and controls roll-over)
        if (wr_en_i = '1' and full_s = '0') then
          if write_index_s = FIFO_DEPTH-1 then
            write_index_s <= 0;
          else
            write_index_s <= write_index_s + 1;
          end if;
        end if;
 
        -- Keeps track of the read index (and controls roll-over)        
        if (rd_en_i = '1' and empty_s = '0') then
          if read_index_s = FIFO_DEPTH-1 then
            read_index_s <= 0;
          else
            read_index_s <= read_index_s + 1;
          end if;
        end if;
 
        -- Registers the input data when there is a write
        if wr_en_i = '1' then
          fifo_data_s(write_index_s) <= wr_data_i;
        end if;
         
      end if;                           -- sync reset
    end if;                             -- rising_edge(clk)
  end process p_CONTROL;
   
  rd_data_o <= fifo_data_s(read_index_s);
 
  full_s  <= '1' when fifo_cnt_s = FIFO_DEPTH else '0';
  empty_s <= '1' when fifo_cnt_s = 0       else '0';
 
  full_o  <= full_s;
  empty_o <= empty_s;

end rtl;