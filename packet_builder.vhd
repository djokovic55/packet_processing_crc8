
library ieee;
use ieee.std_logic_1164.all;

entity packet_builder is
    generic(
        C_M_AXI_BURST_LEN	: integer	:= 16;
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
        crc_val_i: in std_logic_vector(6 downto 0);
        sop_val_i: in std_logic_vector(3 downto 0);
        data_sel_i: in std_logic_vector(3 downto 0);
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
		C_M_AXI_BURST_LEN	: integer	:= 16;
		C_M_AXI_ADDR_WIDTH	: integer	:= 32;
		C_M_AXI_DATA_WIDTH	: integer	:= 32
	);
	port (
    -- SECTION PORTS TO MAIN PACKET_BUILDER
		-- Users to add ports here
    AXI_BASE_ADDRESS_I  : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- base address    
    --  WRITE CHANNEL
    AXI_WRITE_ADDRESS_I : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- address added
    AXI_WRITE_INIT_I    : in  std_logic;  -- start write transactions    
    AXI_WRITE_DATA_I    : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
    AXI_WRITE_VLD_I     : in  std_logic;  --  indicates that write data is valid
    AXI_WRITE_RDY_O     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
    AXI_WRITE_DONE_O    : out std_logic;  -- indicates that burst has finished

    -- READ CHANNEL
    AXI_READ_ADDRESS_I : in std_logic_vector(31 downto 0);  -- address added to base address
    AXI_READ_INIT_I : in  std_logic;    --starts read transaction
    AXI_READ_DATA_O : out std_logic_vector(31 downto 0);  -- data read from                                                             -- ddr
    AXI_READ_VLD_O  : out std_logic;    -- axi_read_data_o is valid
    AXI_READ_RDY_I  : in std_logic;    -- axi_read_data_o is valid
    AXI_READ_LAST_O : out std_logic;    -- axi_read_data_o is valid
		-- User ports ends
		-- Do not modify the ports beyond this line

    -- SECTION INTERCONNECT PORTS 
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
    signal axi_base_address_s  : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- base address    
    --  WRITE CHANNEL
    signal axi_write_address_s : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- address added to base address
    signal axi_write_init_s    : std_logic;  -- start write transactions    
    signal axi_write_data_s    : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
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


begin
  -- [ ] packet_builder1 implementation
  -- [x] master AXI cont added
	axi_base_address_s <= (others => '0');
	axi_write_address_s <= (others => '0');
	axi_write_init_s <= '0';
	axi_write_data_s <= (others => '0');
	axi_write_vld_s <= '0';


	axi_read_address_s <= (others => '0');
	axi_read_init_s <= '0';
	axi_read_data_s <= (others => '0');
	axi_read_rdy_s <= '0';


	seq_logic : process(M_AXI_ACLK)
	begin
      if(M_AXI_ACLK'event and M_AXI_ACLK = '1') then
        if M_AXI_ARESETN = '1' then
					busy_reg <= '1';
				else
					busy_reg <= busy_next;
				end if;
			end if;
	end process;

	comb_logic: process(busy_reg, start_i)
	begin
      if(start_i = '1') then
				busy_next <= '0';
			else
				busy_next <= busy_reg;
			end if;
	end process;

	busy_o <= busy_reg;

  master_axi_cont_ctrl: master_axi_cont
  generic map(
      C_M_AXI_BURST_LEN	=> C_M_AXI_BURST_LEN,
      C_M_AXI_ADDR_WIDTH => C_M_AXI_ADDR_WIDTH,
      C_M_AXI_DATA_WIDTH => C_M_AXI_DATA_WIDTH
  )
  port map(
    --[x] Connect with actual packet_builder1 signals

    AXI_BASE_ADDRESS_I  => axi_base_address_s, 
    AXI_WRITE_ADDRESS_I => axi_write_address_s, 
    AXI_WRITE_INIT_I    => axi_write_init_s, 
    AXI_WRITE_DATA_I    => axi_write_data_s, 
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
