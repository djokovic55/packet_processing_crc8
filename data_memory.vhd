library ieee;
  use ieee.std_logic_1164.all;
  use ieee.numeric_std.all;

entity data_memory is
  generic (

		C_S_AXI_DATA_WIDTH	: integer	:= 32;
		C_S_AXI_ADDR_WIDTH	: integer	:= 32
    
  );
  port (

		-- Global Clock Signal
		S_AXI_ACLK	: in std_logic;
		-- Global Reset Signal. This Signal is Active LOW
		S_AXI_ARESETN	: in std_logic;

		--------------------------------------------------------------------------------
		-- Memory B port - top level use
		--------------------------------------------------------------------------------
		en_b_i	: in std_logic;
		data_b_i	: in std_logic_vector(31 downto 0);
		addr_b_i	: in std_logic_vector(13 downto 0);
		we_b_i	: in std_logic_vector(3 downto 0);
		data_b_o	: out std_logic_vector(31 downto 0);

		--------------------------------------------------------------------------------
		-- SLAVE INTERFACE WRITE ADDRESS
		--------------------------------------------------------------------------------
		-- Write address
		S_AXI_AWADDR	: in std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		-- Burst length. The burst length gives the exact number of transfers in a burst
		S_AXI_AWLEN	: in std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		S_AXI_AWSIZE	: in std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		S_AXI_AWBURST	: in std_logic_vector(1 downto 0);
		-- Write address valid. This signal indicates that
    -- the channel is signaling valid write address and
    -- control information.
		S_AXI_AWVALID	: in std_logic;
		-- Write address ready. This signal indicates that
    -- the slave is ready to accept an address and associated
    -- control signals.
		S_AXI_AWREADY	: out std_logic;

		--------------------------------------------------------------------------------
		-- SLAVE INTERFACE WRITE DATA
		--------------------------------------------------------------------------------
		-- Write Data
		S_AXI_WDATA	: in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
		-- Write strobes. This signal indicates which byte
    -- lanes hold valid data. There is one write strobe
    -- bit for each eight bits of the write data bus.
		S_AXI_WSTRB	: in std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0);
		-- Write last. This signal indicates the last transfer
    -- in a write burst.
		S_AXI_WLAST	: in std_logic;
		-- Write valid. This signal indicates that valid write
    -- data and strobes are available.
		S_AXI_WVALID	: in std_logic;
		-- Write ready. This signal indicates that the slave
    -- can accept the write data.
		S_AXI_WREADY	: out std_logic;

		--------------------------------------------------------------------------------
		-- SLAVE INTERFACE WRITE RESPONSE.
		--------------------------------------------------------------------------------
		-- Write response. This signal indicates the status
    -- of the write transaction.
		S_AXI_BRESP	: out std_logic_vector(1 downto 0);
		-- Write response valid. This signal indicates that the
    -- channel is signaling a valid write response.
		S_AXI_BVALID	: out std_logic;
		-- Response ready. This signal indicates that the master
    -- can accept a write response.
		S_AXI_BREADY	: in std_logic;

		--------------------------------------------------------------------------------
		-- SLAVE INTERFACE READ ADDRESS.
		--------------------------------------------------------------------------------
		-- Read address. This signal indicates the initial
    -- address of a read burst transaction.
		S_AXI_ARADDR	: in std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		-- Burst length. The burst length gives the exact number of transfers in a burst
		S_AXI_ARLEN	: in std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		S_AXI_ARSIZE	: in std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		S_AXI_ARBURST	: in std_logic_vector(1 downto 0);
		-- Write address valid. This signal indicates that
    -- the channel is signaling valid read address and
    -- control information.
		S_AXI_ARVALID	: in std_logic;
		-- Read address ready. This signal indicates that
    -- the slave is ready to accept an address and associated
    -- control signals.
		S_AXI_ARREADY	: out std_logic;

		--------------------------------------------------------------------------------
		-- MASTER READ DATA
		--------------------------------------------------------------------------------
		-- Read Data
		S_AXI_RDATA	: out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
		-- Read response. This signal indicates the status of
    -- the read transfer.
		S_AXI_RRESP	: out std_logic_vector(1 downto 0);
		-- Read last. This signal indicates the last transfer
    -- in a read burst.
		S_AXI_RLAST	: out std_logic;
		-- Read valid. This signal indicates that the channel
    -- is signaling the required read data.
		S_AXI_RVALID	: out std_logic;
		-- Read ready. This signal indicates that the master can
    -- accept the read data and response information.
		S_AXI_RREADY	: in std_logic
  );
end entity;

architecture implementation of data_memory is
  component slave_axi_cont is
	generic (
		-- Users to add parameters here

		-- User parameters ends
		-- Do not modify the parameters beyond this line

		-- Width of S_AXI data bus
		C_S_AXI_DATA_WIDTH	: integer	:= 32;
		-- Width of S_AXI address bus
		C_S_AXI_ADDR_WIDTH	: integer	:= 32
	);
	port (
		-- Users to add ports here
		ADDR_O : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		DATA_O : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
		WR_O : out std_logic_vector(3 downto 0);

		DATA_I : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);

		-- SECTION User ports ends

		-- Do not modify the ports beyond this line

		-- Global Clock Signal
		S_AXI_ACLK	: in std_logic;
		-- Global Reset Signal. This Signal is Active LOW
		S_AXI_ARESETN	: in std_logic;

		--------------------------------------------------------------------------------
		-- SLAVE INTERFACE WRITE ADDRESS
		--------------------------------------------------------------------------------
		-- Write address
		S_AXI_AWADDR	: in std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		-- Burst length. The burst length gives the exact number of transfers in a burst
		S_AXI_AWLEN	: in std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		S_AXI_AWSIZE	: in std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		S_AXI_AWBURST	: in std_logic_vector(1 downto 0);
		-- Write address valid. This signal indicates that
    -- the channel is signaling valid write address and
    -- control information.
		S_AXI_AWVALID	: in std_logic;
		-- Write address ready. This signal indicates that
    -- the slave is ready to accept an address and associated
    -- control signals.
		S_AXI_AWREADY	: out std_logic;

		--------------------------------------------------------------------------------
		-- SLAVE INTERFACE WRITE DATA
		--------------------------------------------------------------------------------
		-- Write Data
		S_AXI_WDATA	: in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
		-- Write strobes. This signal indicates which byte
    -- lanes hold valid data. There is one write strobe
    -- bit for each eight bits of the write data bus.
		S_AXI_WSTRB	: in std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0);
		-- Write last. This signal indicates the last transfer
    -- in a write burst.
		S_AXI_WLAST	: in std_logic;
		-- Write valid. This signal indicates that valid write
    -- data and strobes are available.
		S_AXI_WVALID	: in std_logic;
		-- Write ready. This signal indicates that the slave
    -- can accept the write data.
		S_AXI_WREADY	: out std_logic;

		--------------------------------------------------------------------------------
		-- SLAVE INTERFACE WRITE RESPONSE.
		--------------------------------------------------------------------------------
		-- Write response. This signal indicates the status
    -- of the write transaction.
		S_AXI_BRESP	: out std_logic_vector(1 downto 0);
		-- Write response valid. This signal indicates that the
    -- channel is signaling a valid write response.
		S_AXI_BVALID	: out std_logic;
		-- Response ready. This signal indicates that the master
    -- can accept a write response.
		S_AXI_BREADY	: in std_logic;

		--------------------------------------------------------------------------------
		-- SLAVE INTERFACE READ ADDRESS.
		--------------------------------------------------------------------------------
		-- Read address. This signal indicates the initial
    -- address of a read burst transaction.
		S_AXI_ARADDR	: in std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		-- Burst length. The burst length gives the exact number of transfers in a burst
		S_AXI_ARLEN	: in std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		S_AXI_ARSIZE	: in std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		S_AXI_ARBURST	: in std_logic_vector(1 downto 0);
		-- Write address valid. This signal indicates that
    -- the channel is signaling valid read address and
    -- control information.
		S_AXI_ARVALID	: in std_logic;
		-- Read address ready. This signal indicates that
    -- the slave is ready to accept an address and associated
    -- control signals.
		S_AXI_ARREADY	: out std_logic;

		--------------------------------------------------------------------------------
		-- MASTER READ DATA
		--------------------------------------------------------------------------------
		-- Read Data
		S_AXI_RDATA	: out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
		-- Read response. This signal indicates the status of
    -- the read transfer.
		S_AXI_RRESP	: out std_logic_vector(1 downto 0);
		-- Read last. This signal indicates the last transfer
    -- in a read burst.
		S_AXI_RLAST	: out std_logic;
		-- Read valid. This signal indicates that the channel
    -- is signaling the required read data.
		S_AXI_RVALID	: out std_logic;
		-- Read ready. This signal indicates that the master can
    -- accept the read data and response information.
		S_AXI_RREADY	: in std_logic);

  end component;
  
  component BRAM is
   generic (
    WADDR : natural := 14);
   port(
    clk		: in std_logic;         
		reset : in std_logic;
    en_a_i	: in std_logic;
    en_b_i	: in std_logic;
    data_a_i	: in std_logic_vector(31 downto 0);
    data_b_i	: in std_logic_vector(31 downto 0);
    addr_a_i	: in std_logic_vector(WADDR - 1 downto 0);
    addr_b_i	: in std_logic_vector(WADDR - 1 downto 0);
    we_a_i	: in std_logic_vector(3 downto 0);
    we_b_i	: in std_logic_vector(3 downto 0);
    data_a_o	: out std_logic_vector(31 downto 0);
    data_b_o	: out std_logic_vector(31 downto 0)
    );
  end component;

	-- Signal definitions
	signal data_a_i_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
	signal data_a_o_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
	signal addr_a_s : std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
	signal we_a_s : std_logic_vector(3 downto 0);

begin

  -- [ ] inmem implementation
  -- [x] slave AXI cont added



	inmem_bram: bram 
	generic map(WADDR => 14)
	port map(

    clk	=> S_AXI_ACLK,         
		reset => S_AXI_ARESETN,

    en_a_i => '1',
    data_a_i => data_a_i_s,
    addr_a_i => addr_a_s(13 downto 0),
    we_a_i => we_a_s,
    data_a_o => data_a_o_s,

		-- port b won't be used
    en_b_i => en_b_i,
    data_b_i => data_b_i,
    addr_b_i => addr_b_i,
    we_b_i => we_b_i,
    data_b_o  => data_b_o
	);


  slave_axi_cont_inmem: slave_axi_cont
  generic map(

		C_S_AXI_DATA_WIDTH => C_S_AXI_DATA_WIDTH,	
		C_S_AXI_ADDR_WIDTH => C_S_AXI_ADDR_WIDTH	
  )
  port map(

    ADDR_O => addr_a_s, 
    DATA_O => data_a_i_s, 
    WR_O => we_a_s, 
    DATA_I => data_a_o_s, 

		S_AXI_ACLK => S_AXI_ACLK,	
		S_AXI_ARESETN => S_AXI_ARESETN,	
		S_AXI_AWADDR => S_AXI_AWADDR,	
		S_AXI_AWLEN => S_AXI_AWLEN,	
		S_AXI_AWSIZE => S_AXI_AWSIZE,	
		S_AXI_AWBURST => S_AXI_AWBURST,	
		S_AXI_AWVALID => S_AXI_AWVALID,	
		S_AXI_AWREADY => S_AXI_AWREADY,	
    
		S_AXI_WDATA => S_AXI_WDATA,	
		S_AXI_WSTRB => S_AXI_WSTRB,	
		S_AXI_WLAST => S_AXI_WLAST,	
		S_AXI_WVALID => S_AXI_WVALID,	

		S_AXI_WREADY => S_AXI_WREADY,	
		S_AXI_BRESP => S_AXI_BRESP,	
		S_AXI_BVALID => S_AXI_BVALID,	
		S_AXI_BREADY => S_AXI_BREADY,	

		S_AXI_ARADDR => S_AXI_ARADDR,	
		S_AXI_ARLEN => S_AXI_ARLEN,	
		S_AXI_ARSIZE => S_AXI_ARSIZE,	
		S_AXI_ARBURST => S_AXI_ARBURST,	
		S_AXI_ARVALID => S_AXI_ARVALID,	
		S_AXI_ARREADY => S_AXI_ARREADY,	

		S_AXI_RDATA => S_AXI_RDATA,	
		S_AXI_RRESP => S_AXI_RRESP,	
		S_AXI_RLAST => S_AXI_RLAST,	
		S_AXI_RVALID => S_AXI_RVALID,	
		S_AXI_RREADY => S_AXI_RREADY
  );

end architecture;
