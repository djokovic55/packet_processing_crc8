
library ieee;
use ieee.std_logic_1164.all;
use IEEE.NUMERIC_STD.ALL;

entity packet_builder is
    generic(
        C_M_AXI_ADDR_WIDTH	: integer	:= 32;
        C_M_AXI_DATA_WIDTH	: integer	:= 32
    );
    port (

        -- [x] interface with regs

        start_i : in std_logic;
        busy_o : out std_logic;
        irq_o : out std_logic;
        addr_in_i : in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
        byte_cnt_i : in std_logic_vector(3 downto 0);
        pkt_type_i : in std_logic_vector(3 downto 0);
        ecc_en_i : in std_logic;
        crc_en_i : in std_logic;
        ins_ecc_err_i : in std_logic_vector(1 downto 0);
        ins_crc_err_i : in std_logic;
        ecc_val_i : in std_logic_vector(3 downto 0);
        crc_val_i: in std_logic_vector(7 downto 0);
        sop_val_i: in std_logic_vector(3 downto 0);
        data_sel_i: in std_logic_vector(2 downto 0);
        addr_out_i: in std_logic_vector(31 downto 0);

        -- User ports ends

        --------------------------------------------------------------------------------
        -- Global Clock Signal.
        --------------------------------------------------------------------------------
        M_AXI_ACLK	: in std_logic;
        -- Global Reset Singal. This Signal is Active Low
        M_AXI_ARESETN	: in std_logic;

        --------------------------------------------------------------------------------
        -- MASTER INTERFACE WRITE ADDRESS
        --------------------------------------------------------------------------------
        M_AXI_AWADDR	: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
        -- Burst length. The burst length gives the exact number of transfers in a burst
        M_AXI_AWLEN	: out std_logic_vector(7 downto 0);
        -- Burst size. This signal indicates the size of each transfer in the burst
        M_AXI_AWSIZE	: out std_logic_vector(2 downto 0);
        -- Burst type. The burst type and the size information, 
        -- determine how the address for each transfer within the burst is calculated.
        M_AXI_AWBURST	: out std_logic_vector(1 downto 0);
        -- Write address valid. This signal indicates that
        -- the channel is signaling valid write address and control information.
        M_AXI_AWVALID	: out std_logic;
        -- Write address ready. This signal indicates that
        -- the slave is ready to accept an address and associated control signals
        M_AXI_AWREADY	: in std_logic;

        --------------------------------------------------------------------------------
        -- MASTER INTERFACE WRITE DATA.
        --------------------------------------------------------------------------------
        M_AXI_WDATA	: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
        -- Write strobes. This signal indicates which byte
        -- lanes hold valid data. There is one write strobe
        -- bit for each eight bits of the write data bus.
        M_AXI_WSTRB	: out std_logic_vector(C_M_AXI_DATA_WIDTH/8-1 downto 0);
        -- Write last. This signal indicates the last transfer in a write burst.
        M_AXI_WLAST	: out std_logic;
        -- Write valid. This signal indicates that valid write
        -- data and strobes are available
        M_AXI_WVALID	: out std_logic;
        -- Write ready. This signal indicates that the slave
        -- can accept the write data.
        M_AXI_WREADY	: in std_logic;

        --------------------------------------------------------------------------------
        -- MASTER INTERFACE WRITE RESPONSE.
        --------------------------------------------------------------------------------
        -- m_axi_bid	: in std_logic_vector(c_m_axi_id_width-1 downto 0);
        -- write response. this signal indicates the status of the write transaction.
        M_AXI_BRESP	: in std_logic_vector(1 downto 0);
        -- -- Optional User-defined signal in the write response channel
        -- M_AXI_BUSER	: in std_logic_vector(C_M_AXI_BUSER_WIDTH-1 downto 0);
        -- Write response valid. This signal indicates that the
        -- channel is signaling a valid write response.
        M_AXI_BVALID	: in std_logic;
        -- Response ready. This signal indicates that the master
        -- can accept a write response.
        M_AXI_BREADY	: out std_logic;
        
        --------------------------------------------------------------------------------
        -- MASTER INTERFACE READ ADDRESS.
        --------------------------------------------------------------------------------
        -- Read address. This signal indicates the initial
        -- address of a read burst transaction.
        M_AXI_ARADDR	: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
        -- Burst length. The burst length gives the exact number of transfers in a burst
        M_AXI_ARLEN	: out std_logic_vector(7 downto 0);
        -- Burst size. This signal indicates the size of each transfer in the burst
        M_AXI_ARSIZE	: out std_logic_vector(2 downto 0);
        -- Burst type. The burst type and the size information, 
        -- determine how the address for each transfer within the burst is calculated.
        M_AXI_ARBURST	: out std_logic_vector(1 downto 0);
        -- Write address valid. This signal indicates that
        -- the channel is signaling valid read address and control information
        M_AXI_ARVALID	: out std_logic;
        -- Read address ready. This signal indicates that
        -- the slave is ready to accept an address and associated control signals
        M_AXI_ARREADY	: in std_logic;

        --------------------------------------------------------------------------------
        -- MASTER READ DATA
        --------------------------------------------------------------------------------
        M_AXI_RDATA	: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
        -- Read response. This signal indicates the status of the read transfer
        M_AXI_RRESP	: in std_logic_vector(1 downto 0);
        -- Read last. This signal indicates the last transfer in a read burst
        M_AXI_RLAST	: in std_logic;
        -- Read valid. This signal indicates that the channel
        -- is signaling the required read data.
        M_AXI_RVALID	: in std_logic;
        -- Read ready. This signal indicates that the master can
        -- accept the read data and response information.
        M_AXI_RREADY	: out std_logic

    );
end entity packet_builder;

architecture Behavioral of packet_builder is

  component master_axi_cont is
	generic (
		-- Width of Address Bus
		C_M_AXI_ADDR_WIDTH	: integer	:= 32;
		-- Width of Data Bus
		C_M_AXI_DATA_WIDTH	: integer	:= 32
	);
	port (
		-- Users to add ports here
    AXI_BASE_ADDRESS_I  : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- base address    
		AXI_BURST_LEN : in std_logic_vector(7 downto 0);

    --  WRITE CHANNEL
    AXI_WRITE_INIT_I    : in  std_logic;  -- start write transactions    
    AXI_WRITE_ADDRESS_I : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- address added to base address
    AXI_WRITE_DATA_I    : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		AXI_WRITE_STRB_I    : in  std_logic_vector(3 downto 0);
    AXI_WRITE_VLD_I     : in  std_logic;  --  indicates that write data is valid
    AXI_WRITE_RDY_O     : out std_logic;  -- indicates that controler is ready to accept data
    AXI_WRITE_DONE_O    : out std_logic;  -- indicates that burst has finished

    -- READ CHANNEL
    AXI_READ_INIT_I : in  std_logic;    --starts read transaction
    AXI_READ_ADDRESS_I : in std_logic_vector(31 downto 0);  -- address added to base address
    AXI_READ_DATA_O : out std_logic_vector(31 downto 0);  -- data read from                                                             -- ddr
    AXI_READ_VLD_O  : out std_logic;    -- axi_read_data_o is valid
    AXI_READ_RDY_I  : in std_logic;    -- axi_read_data_o is valid
    AXI_READ_LAST_O : out std_logic;    -- axi_read_data_o is valid
		-- User ports ends

		-- Do not modify the ports beyond this line
		--------------------------------------------------------------------------------
		-- Global Clock Signal.
		--------------------------------------------------------------------------------
		M_AXI_ACLK	: in std_logic;
		-- Global Reset Singal. This Signal is Active Low
		M_AXI_ARESETN	: in std_logic;

		--------------------------------------------------------------------------------
		-- MASTER INTERFACE WRITE ADDRESS
		--------------------------------------------------------------------------------
		M_AXI_AWADDR	: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		-- Burst length. The burst length gives the exact number of transfers in a burst
		M_AXI_AWLEN	: out std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		M_AXI_AWSIZE	: out std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		M_AXI_AWBURST	: out std_logic_vector(1 downto 0);
		-- Write address valid. This signal indicates that
    -- the channel is signaling valid write address and control information.
		M_AXI_AWVALID	: out std_logic;
		-- Write address ready. This signal indicates that
    -- the slave is ready to accept an address and associated control signals
		M_AXI_AWREADY	: in std_logic;

		--------------------------------------------------------------------------------
		-- MASTER INTERFACE WRITE DATA.
		--------------------------------------------------------------------------------
		M_AXI_WDATA	: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		-- Write strobes. This signal indicates which byte
    -- lanes hold valid data. There is one write strobe
    -- bit for each eight bits of the write data bus.
		M_AXI_WSTRB	: out std_logic_vector(C_M_AXI_DATA_WIDTH/8-1 downto 0);
		-- Write last. This signal indicates the last transfer in a write burst.
		M_AXI_WLAST	: out std_logic;
		-- Write valid. This signal indicates that valid write
    -- data and strobes are available
		M_AXI_WVALID	: out std_logic;
		-- Write ready. This signal indicates that the slave
    -- can accept the write data.
		M_AXI_WREADY	: in std_logic;

		--------------------------------------------------------------------------------
		-- MASTER INTERFACE WRITE RESPONSE.
		--------------------------------------------------------------------------------
		-- m_axi_bid	: in std_logic_vector(c_m_axi_id_width-1 downto 0);
		-- write response. this signal indicates the status of the write transaction.
		M_AXI_BRESP	: in std_logic_vector(1 downto 0);
		-- -- Optional User-defined signal in the write response channel
		-- M_AXI_BUSER	: in std_logic_vector(C_M_AXI_BUSER_WIDTH-1 downto 0);
		-- Write response valid. This signal indicates that the
    -- channel is signaling a valid write response.
		M_AXI_BVALID	: in std_logic;
		-- Response ready. This signal indicates that the master
    -- can accept a write response.
		M_AXI_BREADY	: out std_logic;
    
		--------------------------------------------------------------------------------
		-- MASTER INTERFACE READ ADDRESS.
		--------------------------------------------------------------------------------
		-- Read address. This signal indicates the initial
    -- address of a read burst transaction.
		M_AXI_ARADDR	: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		-- Burst length. The burst length gives the exact number of transfers in a burst
		M_AXI_ARLEN	: out std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		M_AXI_ARSIZE	: out std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		M_AXI_ARBURST	: out std_logic_vector(1 downto 0);
		-- Write address valid. This signal indicates that
    -- the channel is signaling valid read address and control information
		M_AXI_ARVALID	: out std_logic;
		-- Read address ready. This signal indicates that
    -- the slave is ready to accept an address and associated control signals
		M_AXI_ARREADY	: in std_logic;

		--------------------------------------------------------------------------------
		-- MASTER READ DATA
		--------------------------------------------------------------------------------
		M_AXI_RDATA	: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		-- Read response. This signal indicates the status of the read transfer
		M_AXI_RRESP	: in std_logic_vector(1 downto 0);
		-- Read last. This signal indicates the last transfer in a read burst
		M_AXI_RLAST	: in std_logic;
		-- Read valid. This signal indicates that the channel
    -- is signaling the required read data.
		M_AXI_RVALID	: in std_logic;
		-- Read ready. This signal indicates that the master can
    -- accept the read data and response information.
		M_AXI_RREADY	: out std_logic
	);
  end component;

  component fifo is
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
  end component;

  component piso is 
  port( 
        clk: in std_logic; 
        reset : in std_logic; --active high reset
        start_piso : in std_logic;
        -- shift : in std_logic;
        d : in std_logic_vector(31 downto 0);
        crc_stall : out std_logic;
        q : out std_logic;
        data_req : out std_logic;

        burst_len : in std_logic_vector(7 downto 0);
        vld_bytes_last_pulse_cnt : in std_logic_vector(1 downto 0)
        ); 
  end component;

  component crc8 is 
  port( 
        clk: in std_logic; 
        reset : in std_logic; --active high reset
        crc_stall : in std_logic;
        size_data : in std_logic_vector(15 downto 0);  --the size of input stream in bits.
        data_in : in std_logic; --serial input
        crc_out : out std_logic_vector(7 downto 0); --8 bit crc checksum
        crc_ready : out std_logic --high when the calculation is done.
        ); 
  end component;

  component hamming_12_8 is 
    Port ( 
      data_in : in  STD_LOGIC_VECTOR(7 downto 0);
      parity_out : out  STD_LOGIC_VECTOR(3 downto 0)
    );
  end component;
  --------------------------------------------------------------------------------
  -- Module connection signals
  --------------------------------------------------------------------------------
  -- Fifo in - READ
  signal fifo_in_wr_en_s   : std_logic;
  signal fifo_in_wr_data_s : std_logic_vector(31 downto 0);
  signal fifo_in_full_s    : std_logic;

  signal fifo_in_rd_pt_rst_s   : std_logic;
  signal fifo_in_rd_en_s   : std_logic;
  signal fifo_in_rd_data_s : std_logic_vector(31 downto 0);
  signal fifo_in_empty_s   : std_logic;
  --------------------------------------------------------------------------------

  -- Fifo in - WRITE
  signal fifo_out_wr_en_s   : std_logic;
  signal fifo_out_wr_data_s : std_logic_vector(31 downto 0);
  signal fifo_out_full_s    : std_logic;

  signal fifo_pt_rst_s   : std_logic;
  signal fifo_out_rd_en_s   : std_logic;
  signal fifo_out_rd_data_s : std_logic_vector(31 downto 0);
  signal fifo_out_empty_s   : std_logic;
  --------------------------------------------------------------------------------

  -- Piso 
  signal start_piso_s : std_logic;
  signal piso_d_s : std_logic_vector(31 downto 0);
  signal piso_q_s : std_logic;
  signal piso_data_req_s : std_logic;

  signal read_burst_len_s : std_logic_vector(7 downto 0) := (others => '0');
  signal vld_bytes_last_pulse_cnt_s : std_logic_vector(1 downto 0);
  signal piso_vld_bytes_last_pulse_cnt_s : std_logic_vector(1 downto 0);
  --------------------------------------------------------------------------------
  -- crc8
  signal crc_stall_s : std_logic;
  signal crc_size_data_s : std_logic_vector(15 downto 0); 
  signal crc_data_in_s : std_logic;
  signal crc_out_s : std_logic_vector(7 downto 0);
  signal crc_ready_s : std_logic; 
  --------------------------------------------------------------------------------
  -- hamming
  signal hamming_data_in_s : STD_LOGIC_VECTOR(7 downto 0);
  signal hamming_parity_out_s : STD_LOGIC_VECTOR(3 downto 0);
  --------------------------------------------------------------------------------


  -- AXI4
  signal axi_burst_len_s  : std_logic_vector(7 downto 0);  
  signal axi_base_address_s  : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- base address    
  --  WRITE CHANNEL
  signal axi_write_address_s : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- address added to base address
  signal axi_write_init_s    : std_logic;  -- start write transactions    
  signal axi_write_data_s    : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
  signal axi_write_strb_s    : std_logic_vector(3 downto 0);
  signal axi_write_vld_s     : std_logic;  --  indicates that write data is valid
  signal axi_write_rdy_s     : std_logic;  -- indicates that controler is ready to                                          -- accept data
  signal axi_write_done_s    : std_logic;  -- indicates that burst has finished
  -- READ CHANNEL

  signal axi_read_address_s : std_logic_vector(31 downto 0);  -- address added to base address
  signal axi_read_init_s : std_logic;    --starts read transaction
  signal axi_read_data_s : std_logic_vector(31 downto 0);  -- data read from                                                             -- ddr
  signal axi_read_vld_s  : std_logic;    -- axi_read_data_o is valid
  signal axi_read_rdy_s  : std_logic;    -- axi_read_data_o is valid
  signal axi_read_last_s : std_logic;    -- axi_read_data_o is valid

  signal busy_reg, busy_next : std_logic;    -- axi_read_data_o is valid

  type state_t is (IDLE, INMEM_READ, CRC_LOOP, BUILD_FIRST_PULSE, BUILD_PULSE, BUILD_LAST_PULSE, BUILD_LONG_LAST_PULSE, OUTMEM_WRITE, OUTMEM_WRITE_LAST);
  signal state_reg, state_next : state_t;
  signal crc_reg, crc_next : std_logic_vector(7 downto 0);
  signal pulse_data_reg, pulse_data_next : std_logic_vector(31 downto 0);
  signal pulse_cnt_reg, pulse_cnt_next : std_logic_vector(7 downto 0);

  signal write_burst_len_s : std_logic_vector(7 downto 0) := (others => '0');
  signal write_byte_cnt : std_logic_vector(4 downto 0) := (others => '0');
  signal single_write_burst : std_logic;


  signal header_s : std_logic_vector(15 downto 0);
  signal ecc_s : std_logic_vector(3 downto 0);

  constant INMEM_BASE_ADDR: unsigned := x"00000000";
  constant OUTMEM_BASE_ADDR: unsigned := x"00010000";


begin
  -- [ ] packet_builder1 implementation
  -- [x] master AXI cont added
  -- calculate read burst len and valid bytes in last pulse based on read_byte_cnt
  read_burst_len_s(7 downto 2) <= (others => '0'); 
  read_burst_len_s(1 downto 0) <= byte_cnt_i(3 downto 2); 

  -- calculate write burst len and valid bytes in last pulse based on write_read_cnt
  write_byte_cnt <= std_logic_vector(to_unsigned(to_integer(unsigned(byte_cnt_i)) + 3, 5)); 
  write_burst_len_s(7 downto 3) <= (others => '0'); 
  write_burst_len_s(2 downto 0) <= write_byte_cnt(4 downto 2);
  vld_bytes_last_pulse_cnt_s <= std_logic_vector(unsigned(write_byte_cnt(1 downto 0)) + 1); 

  -- IMPORTANT byte count from in(read) fifo is needed, which correspond only to data count without header and crc
  piso_vld_bytes_last_pulse_cnt_s <= byte_cnt_i(1 downto 0); 

  single_write_burst <= '1' when write_burst_len_s = "00" else '0';

  -- calculate ecc
  hamming_data_in_s(7 downto 4) <= pkt_type_i;
  hamming_data_in_s(3 downto 0) <= byte_cnt_i;

  ecc_s <= hamming_parity_out_s when ecc_en_i = '1' else 
           ecc_val_i;

  -- form header
  header_s <= sop_val_i&pkt_type_i&byte_cnt_i&ecc_s;

  -- piso data
  piso_d_s <= fifo_in_rd_data_s;


  pb_fsm_seq_proc: process(M_AXI_ACLK)
  begin
      if(M_AXI_ACLK'event and M_AXI_ACLK = '1') then
        if M_AXI_ARESETN = '1' then
          state_reg <= IDLE;
          crc_reg <= (others => '0');
          pulse_data_reg <= (others => '0');
          pulse_cnt_reg <= (others => '0');
        else
          state_reg <= state_next;
          crc_reg <= crc_next;
          pulse_data_reg <= pulse_data_next;
          pulse_cnt_reg <= pulse_cnt_next;
        end if;
      end if;
  end process; 



  pb_fsm_comb_proc:process(state_reg, start_i, addr_in_i, read_burst_len_s, write_burst_len_s,
                           pulse_cnt_reg, pulse_data_reg, crc_reg, crc_ready_s) is
  begin

    -- default values
    state_next <= state_reg;
    crc_next <= crc_reg;
    pulse_cnt_next <= pulse_cnt_reg;
    pulse_data_next <= pulse_data_reg;

    -- AXI defaults
    axi_base_address_s <= (others => '0');
    axi_burst_len_s <= (others => '0');

    axi_write_address_s <= (others => '0');
    axi_write_data_s <= (others => '0');
    axi_write_vld_s <= '0';
    axi_write_strb_s <= (others => '0');
    axi_write_init_s <= '0';

    axi_read_address_s <= (others => '0');
    axi_read_data_s <= (others => '0');
    axi_read_rdy_s <= '0';
    axi_read_init_s <= '0';

    -- Builder default
    busy_o <= '0';
    irq_o <= '0';

    -- FIFOs default
    fifo_in_wr_data_s <= (others => '0');
    fifo_in_wr_en_s <= '0';
    fifo_in_rd_en_s <= '0';

    fifo_out_wr_data_s <= (others => '0');
    fifo_out_wr_en_s <= '0';
    fifo_out_rd_en_s <= '0';

    -- PISO default
    start_piso_s <= '0';

    case state_reg is
      when IDLE =>
        busy_o <= '1';

        if(start_i = '1') then
          ---------------------------------------- 
          state_next <= INMEM_READ;
          ---------------------------------------- 
        else
          ---------------------------------------- 
          state_next <= IDLE;
          ---------------------------------------- 
        end if;
      when INMEM_READ => 
        axi_base_address_s <= std_logic_vector(INMEM_BASE_ADDR);
        axi_read_address_s <= addr_in_i;
        axi_burst_len_s <= read_burst_len_s;

        axi_read_rdy_s <= '1';
        axi_read_init_s <= '1';

        if(axi_read_vld_s = '1') then
          fifo_in_wr_en_s <= '1';
          fifo_in_wr_data_s <= axi_read_data_s;
          
          if(axi_read_last_s = '1') then
            if(crc_en_i = '1') then 

              start_piso_s <= '1';
              ---------------------------------------- 
              state_next <= CRC_LOOP;
              ---------------------------------------- 
            else
              crc_next <= crc_val_i;
              ---------------------------------------- 
              state_next <= BUILD_FIRST_PULSE;
              ---------------------------------------- 
            end if;
          else
            ---------------------------------------- 
            state_next <= INMEM_READ;
            ---------------------------------------- 
          end if;
        else
          ---------------------------------------- 
          state_next <= INMEM_READ;
          ---------------------------------------- 
        end if;

      when CRC_LOOP => 

        if(piso_data_req_s = '1') then
          fifo_in_rd_en_s <= '1';
        end if;

        if(crc_ready_s = '1') then 
          crc_next <= crc_out_s;
          fifo_in_rd_pt_rst_s <= '1';
          ---------------------------------------- 
          state_next <= BUILD_FIRST_PULSE;
          ---------------------------------------- 
        else 
          ---------------------------------------- 
          state_next <= CRC_LOOP;
          ---------------------------------------- 
        end if;
      when BUILD_FIRST_PULSE => 
        -- defaults

        if(unsigned(byte_cnt_i) > 0) then
          -- first pulse in fifo out
          fifo_out_wr_data_s <= header_s&fifo_in_rd_data_s(15 downto 0);
          -- increment write pointer
          fifo_out_wr_en_s <= '1';

          -- store the rest of data for fifo out write iteration
          pulse_data_next <= fifo_in_rd_data_s;
          -- increment read pointer
          fifo_in_rd_en_s <= '1';
          -- increment pulse counter
          pulse_cnt_next <= std_logic_vector(unsigned(pulse_cnt_reg) + 1);

          if(unsigned(pulse_cnt_reg) = unsigned(read_burst_len_s) - 1) then
            ---------------------------------------- 
            state_next <= BUILD_LAST_PULSE;
            ---------------------------------------- 
          else
            ---------------------------------------- 
            state_next <= BUILD_PULSE;
            ---------------------------------------- 
          end if;

          ---------------------------------------- 
          state_next <= OUTMEM_WRITE;
          ---------------------------------------- 
        else
          fifo_out_wr_data_s <= header_s&fifo_in_rd_data_s(7 downto 0)&crc_reg;
          fifo_out_wr_en_s <= '1';
          ---------------------------------------- 
          state_next <= OUTMEM_WRITE;
          ---------------------------------------- 

        end if;
      when BUILD_PULSE => 
        fifo_out_wr_data_s(15 downto 0) <= pulse_data_reg(31 downto 16); 
        fifo_out_wr_data_s(31 downto 16) <= fifo_in_rd_data_s(15 downto 0); 
        fifo_out_wr_en_s <= '1';

        pulse_data_next <= fifo_in_rd_data_s;
        fifo_in_rd_en_s <= '1';

        if(unsigned(pulse_cnt_reg) = unsigned(read_burst_len_s) - 1) then
          ---------------------------------------- 
          state_next <= BUILD_LAST_PULSE;
          ---------------------------------------- 
        else
          ---------------------------------------- 
          state_next <= BUILD_PULSE;
          ---------------------------------------- 
        end if;

      when BUILD_LAST_PULSE => 

        -- first half
        fifo_out_wr_data_s(15 downto 0) <= pulse_data_reg(31 downto 16); 

        case(vld_bytes_last_pulse_cnt_s) is
          when "00" =>
            -- second half
            fifo_out_wr_data_s(23 downto 16) <= crc_reg; 
            fifo_out_wr_data_s(31 downto 24) <= (others => '0'); 
            -- no furter writes

            -- pulse_data_next <= fifo_in_rd_data_s;
            -- no further reads
            ---------------------------------------- 
            state_next <= OUTMEM_WRITE;
            ---------------------------------------- 
          when "01" =>
            -- second half
            fifo_out_wr_data_s(23 downto 16) <= fifo_in_rd_data_s(7 downto 0);
            fifo_out_wr_data_s(31 downto 24) <= crc_reg; 
            -- no furter writes

            -- pulse_data_next <= fifo_in_rd_data_s;
            -- no further reads
            ---------------------------------------- 
            state_next <= OUTMEM_WRITE;
            ---------------------------------------- 
          when  others =>
            fifo_out_wr_data_s(23 downto 16) <= fifo_in_rd_data_s(7 downto 0);
            fifo_out_wr_data_s(31 downto 24) <= fifo_in_rd_data_s(15 downto 8); 
            fifo_out_wr_en_s <= '1';

            pulse_data_next <= fifo_in_rd_data_s;

            -- no further reads
            ---------------------------------------- 
            state_next <= BUILD_LONG_LAST_PULSE;
            ---------------------------------------- 
        end case;
      when BUILD_LONG_LAST_PULSE => 
        -- reset pulse counter because it will be used for write burst
        pulse_cnt_next <= (others => '0');

        case(vld_bytes_last_pulse_cnt_s) is 
          when "10" =>
            fifo_out_wr_data_s(7 downto 0) <= crc_reg; 
            fifo_out_wr_data_s(31 downto 8) <= (others => '0'); 
            
          when others =>
            fifo_out_wr_data_s(7 downto 0) <= pulse_data_reg(23 downto 16); 
            fifo_out_wr_data_s(15 downto 8) <= crc_reg; 
            fifo_out_wr_data_s(31 downto 16) <= (others => '0'); 
        end case;
        ---------------------------------------- 
        state_next <= OUTMEM_WRITE;
        ---------------------------------------- 
      when OUTMEM_WRITE => 
        -- set AW channel
        axi_base_address_s <= std_logic_vector(OUTMEM_BASE_ADDR);
        axi_write_address_s <= addr_out_i;
        axi_burst_len_s <= write_burst_len_s;

        -- set W channel
        axi_write_data_s <= fifo_out_rd_data_s;
        axi_write_strb_s <= "1111";
        axi_write_vld_s <= '1';

        -- start burst 
        axi_write_init_s <= '1';

        if(single_write_burst = '1') then
          if(axi_write_rdy_s = '1') then
            fifo_out_rd_en_s <= '1';
            pulse_cnt_next <= std_logic_vector(unsigned(pulse_cnt_reg) + 1);
            if(unsigned(pulse_cnt_reg) = unsigned(axi_burst_len_s) - 1) then
              ---------------------------------------- 
              state_next <= OUTMEM_WRITE_LAST;
              ---------------------------------------- 
            else
              ---------------------------------------- 
              state_next <= OUTMEM_WRITE;
              ---------------------------------------- 
            end if;
          else 
            ---------------------------------------- 
            state_next <= OUTMEM_WRITE;
            ---------------------------------------- 
          end if;
        else 
          if(axi_write_done_s = '1') then

            irq_o <= '1';
            ---------------------------------------- 
            state_next <= IDLE;
            ---------------------------------------- 
          else
            ---------------------------------------- 
            state_next <= OUTMEM_WRITE;
            ---------------------------------------- 
          end if;
        end if;

      when OUTMEM_WRITE_LAST => 
        -- set AW channel
        axi_base_address_s <= std_logic_vector(OUTMEM_BASE_ADDR);
        axi_write_address_s <= addr_out_i;
        axi_burst_len_s <= write_burst_len_s;

        -- set W channel
        axi_write_data_s <= fifo_out_rd_data_s;
        axi_write_strb_s <= "1111";
        axi_write_vld_s <= '1';

        case(vld_bytes_last_pulse_cnt_s) is 
          when "00" =>
            axi_write_strb_s <= "0001";
          when "01" =>
            axi_write_strb_s <= "0011";
          when "10" =>
            axi_write_strb_s <= "0111";
          when others =>
            axi_write_strb_s <= "1111";
        end case;

        if(axi_write_done_s = '1') then
          irq_o <= '1';
          ---------------------------------------- 
          state_next <= IDLE;
          ---------------------------------------- 
        else
          ---------------------------------------- 
          state_next <= OUTMEM_WRITE_LAST;
          ---------------------------------------- 
        end if;



    end case;
  end process;

  --------------------------------------------------------------------------------
  -- Module instantiations
  --------------------------------------------------------------------------------
  fifo_in: fifo
  port map(

    clk => M_AXI_ACLK,      
    reset => M_AXI_ARESETN, 
    wr_en_i => fifo_in_wr_en_s,   
    wr_data_i => fifo_in_wr_data_s, 
    full_o => fifo_in_full_s,    
    rd_pt_rst => fifo_in_rd_pt_rst_s, 
    rd_en_i => fifo_in_rd_en_s,   
    rd_data_o => fifo_in_rd_data_s, 
    empty_o => fifo_in_empty_s   
  );

  fifo_out: fifo
  port map(

    clk => M_AXI_ACLK,      
    reset => M_AXI_ARESETN, 
    wr_en_i => fifo_out_wr_en_s,   
    wr_data_i => fifo_out_wr_data_s, 
    full_o => fifo_out_full_s,    
    rd_pt_rst => '0',
    rd_en_i => fifo_out_rd_en_s,   
    rd_data_o => fifo_out_rd_data_s, 
    empty_o => fifo_out_empty_s   
  );

  piso_reg: piso
  port map(
    clk => M_AXI_ACLK,      
    reset => M_AXI_ARESETN, 
    start_piso => start_piso_s,
    d => piso_d_s,
    crc_stall => crc_stall_s,
    q => piso_q_s,
    data_req => piso_data_req_s,
    

    burst_len => read_burst_len_s,
    vld_bytes_last_pulse_cnt => piso_vld_bytes_last_pulse_cnt_s
  );

  crc8_calc: crc8
  port map(

    clk => M_AXI_ACLK,      
    reset => M_AXI_ARESETN, 
    crc_stall => crc_stall_s, 
    size_data => crc_size_data_s, 
    data_in => crc_data_in_s, 
    crc_out => crc_out_s, 
    crc_ready => crc_ready_s 
  );
  hamming_calc: hamming_12_8
  port map (
    data_in => hamming_data_in_s,
    parity_out => hamming_parity_out_s
  );


  master_axi_cont_ctrl: master_axi_cont
  generic map(
      C_M_AXI_ADDR_WIDTH => C_M_AXI_ADDR_WIDTH,
      C_M_AXI_DATA_WIDTH => C_M_AXI_DATA_WIDTH
  )
  port map(
    --[x] Connect with actual packet_builder1 signals

    AXI_BURST_LEN  => axi_burst_len_s, 
    AXI_BASE_ADDRESS_I  => axi_base_address_s, 
    AXI_WRITE_ADDRESS_I => axi_write_address_s, 
    AXI_WRITE_INIT_I    => axi_write_init_s, 
    AXI_WRITE_DATA_I    => axi_write_data_s, 
    AXI_WRITE_STRB_I    => axi_write_strb_s,
    AXI_WRITE_VLD_I     => axi_write_vld_s, 
    AXI_WRITE_RDY_O     => axi_write_rdy_s, 
    AXI_WRITE_DONE_O    => axi_write_done_s, 
    AXI_READ_ADDRESS_I => axi_read_address_s, 
    AXI_READ_INIT_I => axi_read_init_s, 
    AXI_READ_DATA_O => axi_read_data_s, 
    AXI_READ_VLD_O  => axi_read_vld_s, 
    AXI_READ_RDY_I  => axi_read_rdy_s, 
    AXI_READ_LAST_O => axi_read_last_s, 

		M_AXI_ACLK => M_AXI_ACLK,	
		M_AXI_ARESETN => M_AXI_ARESETN,	

		M_AXI_AWADDR => M_AXI_AWADDR,	
		M_AXI_AWLEN => M_AXI_AWLEN,	
		M_AXI_AWSIZE => M_AXI_AWSIZE,	
		M_AXI_AWBURST => M_AXI_AWBURST,	
		M_AXI_AWVALID => M_AXI_AWVALID,	
		M_AXI_AWREADY => M_AXI_AWREADY,	

		M_AXI_WDATA => M_AXI_WDATA,	
		M_AXI_WSTRB => M_AXI_WSTRB,	
		M_AXI_WLAST => M_AXI_WLAST,	
		M_AXI_WVALID => M_AXI_WVALID,	
		M_AXI_WREADY => M_AXI_WREADY,	

		M_AXI_BRESP => M_AXI_BRESP,	
		M_AXI_BVALID => M_AXI_BVALID,	
		M_AXI_BREADY => M_AXI_BREADY,	
    
		M_AXI_ARADDR => M_AXI_ARADDR,	
		M_AXI_ARLEN => M_AXI_ARLEN,	
		M_AXI_ARSIZE => M_AXI_ARSIZE,	
		M_AXI_ARBURST => M_AXI_ARBURST,	
		M_AXI_ARVALID => M_AXI_ARVALID,	
		M_AXI_ARREADY => M_AXI_ARREADY,	

		M_AXI_RDATA => M_AXI_RDATA,	
		M_AXI_RRESP => M_AXI_RRESP,	
		M_AXI_RLAST => M_AXI_RLAST,	
		M_AXI_RVALID => M_AXI_RVALID,	
		M_AXI_RREADY => M_AXI_RREADY
  );

end architecture Behavioral;
