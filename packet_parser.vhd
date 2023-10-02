library ieee;
use ieee.std_logic_1164.all;
use IEEE.NUMERIC_STD.ALL;

entity packet_parser is
    generic(
        C_M_AXI_ADDR_WIDTH	: integer	:= 32;
        C_M_AXI_DATA_WIDTH	: integer	:= 32
    );
    port (

        -- INTERRUPT PORTS
        -- FIXME interface with regs
        start_i : in std_logic;
        busy_o : out std_logic;
        irq_o : out std_logic;
        addr_hdr_i : in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
        ignore_ecc_err_i : in std_logic;
        pkt_ecc_corr_o : out std_logic;
        pkt_ecc_uncorr_o : out std_logic;
        pkt_crc_err_o : out std_logic;
        pkt_byte_cnt_o : out std_logic_vector(3 downto 0);
        pkt_type_o : out std_logic_vector(3 downto 0);

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
end entity packet_parser;

architecture Behavioral of packet_parser is

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

  constant INMEM_BASE_ADDR: unsigned := x"00000000";
  type state_t is (IDLE, HEADER_READ, INMEM_READ, CRC_LOOP);
  signal state_reg, state_next : state_t;

  signal crc_reg, crc_next : std_logic_vector(7 downto 0);
  signal header_reg, header_next : std_logic_vector(15 downto 0);
  signal byte_cnt_with_crc_s : std_logic_vector(4 downto 0);

  -- register output signals
  signal busy_o_reg, busy_o_next  : std_logic;
  -- signal irq_o_reg, irq_o_next  : std_logic;
  signal pkt_ecc_corr_o_reg, pkt_ecc_corr_o_next  : std_logic;
  signal pkt_ecc_uncorr_o_reg, pkt_ecc_uncorr_o_next  : std_logic;
  signal pkt_crc_err_o_reg, pkt_crc_err_o_next  : std_logic;
  signal pkt_byte_cnt_o_reg, pkt_byte_cnt_o_next: std_logic_vector(3 downto 0);
  signal pkt_type_o_reg, pkt_type_o_next  : std_logic_vector(3 downto 0);

  -- Fifo in - WRITE
  signal fifo_in_wr_en_s   : std_logic;
  signal fifo_in_wr_data_s : std_logic_vector(31 downto 0);
  signal fifo_in_full_s    : std_logic;

  signal fifo_in_rd_pt_rst_s   : std_logic;
  signal fifo_in_rd_en_s   : std_logic;
  signal fifo_in_rd_data_s : std_logic_vector(31 downto 0);
  signal fifo_in_empty_s   : std_logic;
  --------------------------------------------------------------------------------

  -- Piso 
  signal start_piso_s : std_logic;
  signal piso_d_s : std_logic_vector(31 downto 0);
  signal piso_q_s : std_logic;
  signal piso_data_req_s : std_logic;

  signal burst_len_s : std_logic_vector(7 downto 0) := (others => '0');
  signal burst_len_with_crc_s: std_logic_vector(7 downto 0) := (others => '0');
  signal piso_vld_bytes_last_pulse_cnt_s : std_logic_vector(1 downto 0);
  --------------------------------------------------------------------------------
  -- crc8
  signal crc_stall_s : std_logic;
  signal crc_size_data_s : std_logic_vector(15 downto 0); 
  signal crc_data_in_s : std_logic;
  signal crc_out_s : std_logic_vector(7 downto 0);
  signal crc_ready_s : std_logic; 

  signal crc_pos_s : std_logic_vector(1 downto 0);
  signal crc_err_s : std_logic;
  --------------------------------------------------------------------------------
  -- hamming
  signal hamming_data_in_s : STD_LOGIC_VECTOR(7 downto 0);
  signal hamming_parity_out_s : STD_LOGIC_VECTOR(3 downto 0);
  signal ecc_err : std_logic;
  --------------------------------------------------------------------------------

begin
  -- [ ] packet_parser implementation
  -- [x] master AXI cont added
  -- output signals

  pkt_ecc_corr_o <= pkt_ecc_corr_o_reg;
  pkt_ecc_uncorr_o <= pkt_ecc_uncorr_o_reg;
  pkt_crc_err_o <= pkt_crc_err_o_reg;
  pkt_byte_cnt_o <= pkt_byte_cnt_o_reg;
  pkt_type_o <= pkt_type_o_reg;

  -- piso data
  piso_d_s <= fifo_in_rd_data_s;

  -- calculate burst len and valid bytes in last pulse based on byte_cnt + 1 (crc8)
  byte_cnt_with_crc_s <= std_logic_vector(to_unsigned(to_integer(unsigned(pkt_byte_cnt_o_reg)) + 1, 5)); 
  burst_len_with_crc_s(7 downto 3) <= (others => '0');
  burst_len_with_crc_s(2 downto 0) <= byte_cnt_with_crc_s(4 downto 2);
  crc_pos_s <= std_logic_vector(unsigned(byte_cnt_with_crc_s(1 downto 0))); 


  -- without crc, used in piso to calculate crc
  burst_len_s(7 downto 4) <= (others => '0');
  burst_len_s(1 downto 0) <= pkt_byte_cnt_o_reg(3 downto 2);
  piso_vld_bytes_last_pulse_cnt_s <= std_logic_vector(unsigned(pkt_byte_cnt_o_reg(1 downto 0))); 



  pp_fsm_seq_proc: process(M_AXI_ACLK)
  begin
      if(M_AXI_ACLK'event and M_AXI_ACLK = '1') then
        if M_AXI_ARESETN = '1' then
          state_reg <= IDLE;
          crc_reg <= (others => '0');
          header_reg <= (others => '0');

          -- busy_o_reg <= '0';
          -- irq_o_reg <= '0';
          pkt_ecc_corr_o_reg <= '0';
          pkt_ecc_uncorr_o_reg <= '0';
          pkt_crc_err_o_reg <= '0';
          pkt_byte_cnt_o_reg <= (others => '0');
          pkt_type_o_reg <= (others => '0');
        else
          state_reg <= state_next;
          crc_reg <= crc_next;
          header_reg <= header_next;

          -- busy_o_reg <= busy_o_next;
          -- irq_o_reg <= irq_o_next;
          pkt_ecc_corr_o_reg <= pkt_ecc_corr_o_next;
          pkt_ecc_uncorr_o_reg <= pkt_ecc_uncorr_o_next;
          pkt_crc_err_o_reg <= pkt_crc_err_o_next;
          pkt_byte_cnt_o_reg <= pkt_byte_cnt_o_next;
          pkt_type_o_reg <= pkt_type_o_next;

        end if;
      end if;
  end process; 



  pp_fsm_comb_proc:process(state_reg, start_i, addr_hdr_i, burst_len_s, burst_len_with_crc_s,
                           crc_reg, crc_ready_s, header_reg) is
  begin
    -- top interface 
    -- [x] pkt_type, pkt_byte_cnt and other outputs logic

    -- default values
    state_next <= state_reg;
    crc_next <= crc_reg;
    header_next <= header_reg;
    
    -- busy_o_next <= busy_o_reg;
    -- irq_o_next <= irq_o_reg;
    irq_o <= '1';

    pkt_ecc_corr_o_next <= pkt_ecc_corr_o_reg;
    pkt_ecc_uncorr_o_next <= pkt_ecc_uncorr_o_reg;
    pkt_crc_err_o_next <= pkt_crc_err_o_reg;
    pkt_byte_cnt_o_next <= pkt_byte_cnt_o_reg;
    pkt_type_o_next <= pkt_type_o_reg;

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

    -- FIFOs default
    fifo_in_wr_data_s <= (others => '0');
    fifo_in_wr_en_s <= '0';
    fifo_in_rd_en_s <= '0';

    -- PISO default
    start_piso_s <= '0';

    -- ECC default
    hamming_data_in_s <= (others => '0');
    ecc_err <= '0';

    case state_reg is
      when IDLE =>
        -- reset all regs values
        pkt_ecc_corr_o_next <= '0';
        pkt_ecc_uncorr_o_next <= '0';
        pkt_crc_err_o_next <= '0';
        pkt_byte_cnt_o_next <= (others => '0');
        pkt_type_o_next <= (others => '0');

        busy_o <= '1';

        if(start_i = '1') then
          ---------------------------------------- 
          state_next <= HEADER_READ;
          ---------------------------------------- 
        else
          ---------------------------------------- 
          state_next <= IDLE;
          ---------------------------------------- 
        end if;
      
      when HEADER_READ => 
        axi_base_address_s <= std_logic_vector(INMEM_BASE_ADDR);
        axi_read_address_s <= addr_hdr_i;
        axi_burst_len_s <= (others => '0');

        axi_read_rdy_s <= '1';
        axi_read_init_s <= '1';

        if(axi_read_vld_s = '1' and axi_read_last_s = '1') then
          -- header won't be stored in fifo, then in its register
          -- fifo_in_wr_en_s <= '1';
          -- fifo_in_wr_data_s <= axi_read_data_s;
          header_next <= axi_read_data_s(15 downto 0);

          -- IMPORTANT check received and calculated ecc code

          -- parse packet type
          hamming_data_in_s(7 downto 4) <= axi_read_data_s(11 downto 8);
          -- parse byte count
          hamming_data_in_s(3 downto 0) <= axi_read_data_s(7 downto 4);
          pkt_byte_cnt_o_next <= axi_read_data_s(7 downto 4);

          if(unsigned(axi_read_data_s(3 downto 0)) /= unsigned(hamming_parity_out_s)) then
            -- KEY here must be decided whether the is corr or uncorr ecc error
            ecc_err <= '0';
            -- [ ] set output signals about corr and uncorr error
            -- pkt_ecc_uncorr_o_next <= '1';
            -- pkt_ecc_corr_o_next <= '1';
            ---------------------------------------- 
            state_next <= INMEM_READ;
            ---------------------------------------- 
          else
            ecc_err <= '1';
            -- check if error can be ignored and preceed to inmmem read or finish task
            if(ignore_ecc_err_i = '1') then
              ---------------------------------------- 
              state_next <= INMEM_READ;
              ---------------------------------------- 
            else
              irq_o <= '1';
              ---------------------------------------- 
              state_next <= IDLE;
              ---------------------------------------- 
            end if;
          end if;


        else
          ---------------------------------------- 
          state_next <= HEADER_READ;
          ---------------------------------------- 
        end if;

      when INMEM_READ => 
        axi_base_address_s <= std_logic_vector(INMEM_BASE_ADDR);
        -- IMPORTANT 2 bytes of header are already read, so continue reading from first data byte to and including crc byte
        axi_read_address_s <= std_logic_vector(unsigned(addr_hdr_i) + 2);
        axi_burst_len_s <= burst_len_with_crc_s;

        axi_read_rdy_s <= '1';
        axi_read_init_s <= '1';

        if(axi_read_vld_s = '1') then
          fifo_in_wr_en_s <= '1';
          fifo_in_wr_data_s <= axi_read_data_s;
          
          if(axi_read_last_s = '1') then
              -- IMPORTANT parse crc8

              crc_next <= axi_read_data_s((to_integer(unsigned(crc_pos_s))*8) + 7 downto (to_integer(unsigned(crc_pos_s))*8));
              start_piso_s <= '1';
              ---------------------------------------- 
              state_next <= CRC_LOOP;
              ---------------------------------------- 
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
          -- IMPORTANT in crc reg is stored read crc
          -- crc_next <= crc_out_s;
          if(unsigned(crc_reg) /= unsigned(crc_out_s)) then
            crc_err_s <= '1';
            -- [x] set output signals about crc error
            pkt_crc_err_o_next <= '1';
          end if;

          irq_o <= '1';
          ---------------------------------------- 
          state_next <= IDLE;
          ---------------------------------------- 
        else 
          ---------------------------------------- 
          state_next <= CRC_LOOP;
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

  piso_reg: piso
  port map(
    clk => M_AXI_ACLK,      
    reset => M_AXI_ARESETN, 
    start_piso => start_piso_s,
    d => piso_d_s,
    crc_stall => crc_stall_s,
    q => piso_q_s,
    data_req => piso_data_req_s,
    

    burst_len => burst_len_s,
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
    --FIXME Connect with actual packet_parser signals

    AXI_BURST_LEN  => axi_burst_len_s, 

    AXI_BASE_ADDRESS_I  => axi_base_address_s, 
    AXI_WRITE_ADDRESS_I => axi_write_address_s, 
    AXI_WRITE_INIT_I    => axi_write_init_s, 
    AXI_WRITE_DATA_I    => axi_write_data_s, 
    AXI_WRITE_VLD_I     => axi_write_vld_s, 
    AXI_WRITE_STRB_I    => axi_write_strb_s,
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
