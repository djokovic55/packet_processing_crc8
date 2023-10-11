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

  component crc_top is 
  port( 
    clk: in std_logic; 
    reset : in std_logic; --active high reset
    
    start_crc : in std_logic;
    pulse_cnt_max : in std_logic_vector(1 downto 0);
    vld_bytes_last_pulse_cnt : in std_logic_vector(1 downto 0);

    data_in : in std_logic_vector(31 downto 0);
    data_req: out std_logic;
    crc_out : out std_logic_vector(7 downto 0);
    crc_ready : out std_logic
    ); 
  end component crc_top; 

component hamming_check is
    Port ( 
           data_in : in  std_logic_vector(7 downto 0);
           parity_in : in  std_logic_vector(3 downto 0);
           parity_check_out : out std_logic_vector(3 downto 0));
end component hamming_check;

  -- Axi4
  signal axi_burst_len_s  : std_logic_vector(7 downto 0);  
  signal axi_base_address_s  : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);

  -- write channel
  signal axi_write_address_s : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
  signal axi_write_init_s    : std_logic;
  signal axi_write_data_s    : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
  signal axi_write_strb_s    : std_logic_vector(3 downto 0);
  signal axi_write_vld_s     : std_logic;
  signal axi_write_rdy_s     : std_logic;
  signal axi_write_done_s    : std_logic;

  -- read channel
  signal axi_read_address_s : std_logic_vector(31 downto 0);
  signal axi_read_init_s : std_logic;
  signal axi_read_data_s : std_logic_vector(31 downto 0);
  signal axi_read_vld_s  : std_logic;
  signal axi_read_rdy_s  : std_logic;
  signal axi_read_last_s : std_logic;
  --------------------------------------------------------------------------------

  constant INMEM_BASE_ADDR: unsigned := x"00000000";
  type state_t is (IDLE, HEADER_READ, INMEM_READ, CRC_LOOP);
  signal state_reg, state_next : state_t;

  signal crc_reg, crc_next : std_logic_vector(7 downto 0);
  signal header_reg, header_next : std_logic_vector(15 downto 0);
  signal byte_cnt_with_crc_s : std_logic_vector(4 downto 0);

  -- register output signals
  signal busy_o_reg, busy_o_next  : std_logic;
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

  -- crc8 signals
  signal start_crc_s : std_logic;
  signal shift_data_in_s : std_logic_vector(31 downto 0);
  signal shift_data_req_s : std_logic;

  signal crc_out_s : std_logic_vector(7 downto 0);
  signal crc_ready_s : std_logic; 

  signal read_burst_len_s : std_logic_vector(7 downto 0) := (others => '0');

  signal crc_pos_s : std_logic_vector(1 downto 0);
  signal crc_err_s : std_logic;

  signal burst_len_with_crc_s: std_logic_vector(7 downto 0) := (others => '0');
  --------------------------------------------------------------------------------
  -- hamming
  signal hamming_data_in_s : std_logic_vector(7 downto 0);
  signal hamming_parity_in_s : std_logic_vector(3 downto 0);
  signal hamming_msb_parity_bit_s : std_logic;
  signal hamming_parity_check_out_s : std_logic_vector(3 downto 0);
  --------------------------------------------------------------------------------
  -- header data
  -- signal pkt_byte_cnt

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
  shift_data_in_s <= fifo_in_rd_data_s;

  -- calculate burst len and valid bytes in last pulse based on byte_cnt + 1 (crc8)
  byte_cnt_with_crc_s <= std_logic_vector(to_unsigned(to_integer(unsigned(pkt_byte_cnt_o_reg)) + 1, 5)); 
  burst_len_with_crc_s(7 downto 3) <= (others => '0');
  burst_len_with_crc_s(2 downto 0) <= byte_cnt_with_crc_s(4 downto 2);
  crc_pos_s <= std_logic_vector(unsigned(byte_cnt_with_crc_s(1 downto 0))); 

  pp_fsm_seq_proc: process(M_AXI_ACLK)
  begin
      if(M_AXI_ACLK'event and M_AXI_ACLK = '1') then
        if M_AXI_ARESETN = '1' then
          state_reg <= IDLE;
          crc_reg <= (others => '0');
          header_reg <= (others => '0');

          pkt_ecc_corr_o_reg <= '0';
          pkt_ecc_uncorr_o_reg <= '0';
          pkt_crc_err_o_reg <= '0';
          pkt_byte_cnt_o_reg <= (others => '0');
          pkt_type_o_reg <= (others => '0');
        else
          state_reg <= state_next;
          crc_reg <= crc_next;
          header_reg <= header_next;

          pkt_ecc_corr_o_reg <= pkt_ecc_corr_o_next;
          pkt_ecc_uncorr_o_reg <= pkt_ecc_uncorr_o_next;
          pkt_crc_err_o_reg <= pkt_crc_err_o_next;
          pkt_byte_cnt_o_reg <= pkt_byte_cnt_o_next;
          pkt_type_o_reg <= pkt_type_o_next;

        end if;
      end if;
  end process; 



  pp_fsm_comb_proc:process(state_reg, header_reg, pkt_ecc_corr_o_reg, pkt_ecc_uncorr_o_reg, 
                           pkt_crc_err_o_reg, pkt_byte_cnt_o_reg, pkt_type_o_reg, axi_read_data_s, 
                           axi_read_vld_s, axi_read_last_s, hamming_parity_in_s, ignore_ecc_err_i, 
													 start_i, addr_hdr_i, burst_len_with_crc_s, crc_reg, crc_ready_s) is
  begin
    -- top interface 
    -- [x] pkt_type, pkt_byte_cnt and other outputs logic

    -- default values
    state_next <= state_reg;
    crc_next <= crc_reg;
    header_next <= header_reg;
    
    irq_o <= '0';

    -- output regs
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

    -- Crc default
    start_crc_s <= '0';

    -- ECC default
    hamming_data_in_s <= (others => '0');
    hamming_parity_in_s <= (others => '0');
    hamming_msb_parity_bit_s <= '0';

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
          header_next <= axi_read_data_s(15 downto 0);
          -- parse packet type
          hamming_data_in_s(7 downto 4) <= axi_read_data_s(11 downto 8);
          -- parse byte count
          hamming_data_in_s(3 downto 0) <= axi_read_data_s(7 downto 4);
          -- parse parity bits
          hamming_parity_in_s <= axi_read_data_s(3 downto 0);
          -- parse msb parity bit
          hamming_msb_parity_bit_s <= axi_read_data_s(12);


          -- KEY informations which must be correct
          pkt_byte_cnt_o_next <= axi_read_data_s(7 downto 4);
          pkt_type_o_next <= axi_read_data_s(11 downto 8);

          -- IMPORTANT check for single or double ecc errors
          if(unsigned(hamming_parity_check_out_s) = "0000") then
            -- no error
            pkt_ecc_uncorr_o_next <= '0';
            pkt_ecc_corr_o_next <= '0';
            ---------------------------------------- 
            state_next <= INMEM_READ;
            ---------------------------------------- 
          else
            -- check if error can be ignored and preceed to inmmem read or finish task
            if(hamming_msb_parity_bit_s = '1') then
              -- IMPORTANT single ecc error correction logic
              case(hamming_parity_check_out_s) is 
                when "0011" => --m0
                  pkt_byte_cnt_o_next(0) <= not(axi_read_data_s(4));
                when "0101" => --m1
                  pkt_byte_cnt_o_next(1) <= not(axi_read_data_s(5));
                when "0110" => --m2
                  pkt_byte_cnt_o_next(2) <= not(axi_read_data_s(6));
                when "0111" => --m3
                  pkt_byte_cnt_o_next(3) <= not(axi_read_data_s(7));
                when "1001" => --m4
                  pkt_type_o_next(0) <= not(axi_read_data_s(8));
                when "1010" => --m5
                  pkt_type_o_next(1) <= not(axi_read_data_s(9));
                when "1011" => --m6
                  pkt_type_o_next(2) <= not(axi_read_data_s(10));
                when "1100" => --m7
                  pkt_type_o_next(3) <= not(axi_read_data_s(11));
                when others => -- parity bits which does not need to be corrected
              end case;
            else 
              -- double ecc error
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
        -- IMPORTANT axi burst len depends on byte_cnt, therefore inmem read phase will fail if this information is incorrect
        axi_burst_len_s <= burst_len_with_crc_s;

        axi_read_rdy_s <= '1';
        axi_read_init_s <= '1';

        if(axi_read_vld_s = '1') then
          fifo_in_wr_en_s <= '1';
          fifo_in_wr_data_s <= axi_read_data_s;
          
          if(axi_read_last_s = '1') then

              -- IMPORTANT parse crc8
						  case crc_pos_s is
								when "00" =>
              		crc_next <= axi_read_data_s(7 downto 0);
								when "01" =>
              		crc_next <= axi_read_data_s(15 downto 8);
								when "10" =>
              		crc_next <= axi_read_data_s(23 downto 16);
								when others =>
              		crc_next <= axi_read_data_s(31 downto 24);
							end case;

              start_crc_s <= '1';
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

        if(shift_data_req_s= '1') then
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

  crc_calc: crc_top
  port map(
    clk => M_AXI_ACLK,      
    reset => M_AXI_ARESETN, 
    start_crc => start_crc_s,
    pulse_cnt_max => pkt_byte_cnt_o_reg(3 downto 2),
    vld_bytes_last_pulse_cnt => pkt_byte_cnt_o_reg(1 downto 0),

    data_in => shift_data_in_s,
    data_req => shift_data_req_s,
    crc_out => crc_out_s, 
    crc_ready => crc_ready_s
  );

  hamming_chk: hamming_check
  port map (
    data_in => hamming_data_in_s,
    parity_in => hamming_parity_in_s,
    parity_check_out => hamming_parity_check_out_s 
  );
  master_axi_cont_ctrl: master_axi_cont
  generic map(
      C_M_AXI_ADDR_WIDTH => C_M_AXI_ADDR_WIDTH,
      C_M_AXI_DATA_WIDTH => C_M_AXI_DATA_WIDTH
  )
  port map(

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
