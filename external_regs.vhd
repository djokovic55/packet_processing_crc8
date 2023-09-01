
library ieee;
  use ieee.std_logic_1164.all;
  use ieee.numeric_std.all;

entity external_regs is
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

		-- FIXME Delete users ports 
		-- ADDR_O : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		-- DATA_O : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
		-- WR_O : out std_logic;

		-- DATA_I : in std_logic_vector(C_S_AXI_DATA_WIDTH downto 0);
		-- User ports ends

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
		S_AXI_RREADY	: in std_logic
  );
end entity;

architecture implementation of external_regs is

  component slave_axi_lite_ex_regs_cont is
  generic (
  -- Users to add parameters here
  -- Width of S_AXI data bus
  C_S_AXI_DATA_WIDTH : integer := 32;
  -- Width of S_AXI address bus
  C_S_AXI_ADDR_WIDTH : integer := 32);

 port (
  -- Users to add ports here
  -- RO registers
  reg_data_o : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
	ext_pb_ctrl1_wr_o : out std_logic; -- irq_line_0

	ext_pp_ctrl1_wr_o : out std_logic;
	ext_drop_cnt_wr_o : out std_logic;

	ext_pb_ctrl1_i : in std_logic; -- irq_line_0
	ext_pb_ctrl2_i : in std_logic_vector(31 downto 0); -- in_addr
	ext_pb_ctrl3_i : in std_logic_vector(31 downto 0);
	ext_pb_ctrl4_i : in std_logic_vector(31 downto 0);

	ext_pp_ctrl1_i : in std_logic;
	ext_pp_ctrl2_i : in std_logic_vector(31 downto 0);
	ext_pp_ctrl3_i : in std_logic;

	ext_drop_cnt_i : in std_logic_vector(31 downto 0);
  -- User ports ends
  -- Do not modify the ports beyond this line
  S_AXI_ACLK : in std_logic;
  S_AXI_ARESETN : in std_logic;

  S_AXI_AWADDR : in std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
  -- S_AXI_AWPROT : in std_logic_vector(2 downto 0);
  S_AXI_AWVALID : in std_logic;
  S_AXI_AWREADY : out std_logic;

  S_AXI_WDATA : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
  S_AXI_WSTRB : in std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0);
  S_AXI_WVALID : in std_logic;
  S_AXI_WREADY : out std_logic;

  S_AXI_BRESP : out std_logic_vector(1 downto 0);
  S_AXI_BVALID : out std_logic;
  S_AXI_BREADY : in std_logic;

  S_AXI_ARADDR : in std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
  -- S_AXI_ARPROT : in std_logic_vector(2 downto 0);
  S_AXI_ARVALID : in std_logic;
  S_AXI_ARREADY : out std_logic;

  S_AXI_RDATA : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
  S_AXI_RRESP : out std_logic_vector(1 downto 0);
  S_AXI_RVALID : out std_logic;
  S_AXI_RREADY : in std_logic);

  end component;
  
	-- Input
	signal reg_data_s : std_logic_vector(31 downto 0); -- in_addr

	signal ext_pb_ctrl1_wr_s: std_logic; 
	signal ext_pp_ctrl1_wr_s : std_logic; 
	signal ext_drop_cnt_wr_s : std_logic;

	-- Output
	-- IMPORTANT _conf signals will be used to set up RO registers

	signal ext_pb_ctrl1_s : std_logic; -- W1C
	signal ext_pb_ctrl1_conf : std_logic; -- W1C

	signal ext_pb_ctrl2_s : std_logic_vector(31 downto 0);  -- RO
	signal ext_pb_ctrl2_conf : std_logic_vector(31 downto 0); 

	signal ext_pb_ctrl3_s : std_logic_vector(31 downto 0); -- RO
	signal ext_pb_ctrl3_conf : std_logic_vector(31 downto 0);

	signal ext_pb_ctrl4_s : std_logic_vector(31 downto 0); -- RO
	signal ext_pb_ctrl4_conf : std_logic_vector(31 downto 0);

	signal ext_pp_ctrl1_s : std_logic; -- W1C
	signal ext_pp_ctrl1_conf : std_logic; -- W1C

	signal ext_pp_ctrl2_s : std_logic_vector(31 downto 0); -- RO
	signal ext_pp_ctrl2_conf : std_logic_vector(31 downto 0); 

	signal ext_pp_ctrl3_s : std_logic; -- RO
	signal ext_pp_ctrl3_conf : std_logic;

	signal ext_drop_cnt_s : std_logic_vector(31 downto 0); -- RW

begin

  -- [x] slave AXI cont added
  -- [x] external_regs implementation
  -- [x] AXI cont update to lite version
	--------------------------------------------------------------------------------	
	-- Registers
	--------------------------------------------------------------------------------	
	-- W1C
	ext_pb_ctrl1: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				ext_pb_ctrl1_s <= '0';
			elsif ext_pb_ctrl1_wr_s = '1' then
				if(reg_data_s(0) = '1') then
					ext_pb_ctrl1_s <= '0';
				end if;
			else 
				ext_pb_ctrl1_s <= ext_pb_ctrl1_conf;
			end if;
		end if;
	end process;
	--------------------------------------------------------------------------------	
	
	ext_pb_ctrl2: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				ext_pb_ctrl2_s <= (others => '0');
			else
				ext_pb_ctrl2_s <= ext_pb_ctrl2_conf ;
			end if;
		end if;
	end process;
	--------------------------------------------------------------------------------	

	ext_pb_ctrl3: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				ext_pb_ctrl3_s <= (others => '0');
			else
				ext_pb_ctrl3_s <= ext_pb_ctrl3_conf ;
			end if;
		end if;
	end process;
	--------------------------------------------------------------------------------	

	ext_pb_ctrl4: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				ext_pb_ctrl4_s <= (others => '0');
			else
				ext_pb_ctrl4_s <= ext_pb_ctrl4_conf ;
			end if;
		end if;
	end process;
	--------------------------------------------------------------------------------	
	
	-- W1C
	ext_pp_ctrl1: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				ext_pp_ctrl1_s <= '0';
			elsif ext_pp_ctrl1_wr_s = '1' then
				if(reg_data_s(0) = '1') then
					ext_pp_ctrl1_s <= '0';
				end if;
			else 
				ext_pp_ctrl1_s <= ext_pp_ctrl1_conf;
			end if;
		end if;
	end process;
	--------------------------------------------------------------------------------	

	ext_pp_ctrl2: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				ext_pp_ctrl2_s <= (others => '0');
			else
				ext_pp_ctrl2_s <= ext_pp_ctrl2_conf ;
			end if;
		end if;
	end process;
	--------------------------------------------------------------------------------	

	ext_pp_ctrl3: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				ext_pp_ctrl3_s <= '0';
			else
				ext_pp_ctrl3_s <= ext_pp_ctrl3_conf ;
			end if;
		end if;
	end process;
	--------------------------------------------------------------------------------	

	ext_drop_cnt: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				ext_drop_cnt_s <= (others => '0');
			elsif ext_drop_cnt_wr_s = '1' then
				ext_drop_cnt_s <= reg_data_s;
			end if;
		end if;
	end process;

  ex_regs_cont: slave_axi_lite_ex_regs_cont
  generic map(

		C_S_AXI_DATA_WIDTH => C_S_AXI_DATA_WIDTH,	
		C_S_AXI_ADDR_WIDTH => C_S_AXI_ADDR_WIDTH	
  )
  port map(

    -- FIXME Connect with actual memory ports
    -- ADDR_O => open, 
    -- DATA_O => open, 
    -- WR_O => open, 
    -- DATA_I => (others => '0'), 

		reg_data_o => reg_data_s,

		ext_pb_ctrl1_wr_o => ext_pb_ctrl1_wr_s,
		ext_pp_ctrl1_wr_o => ext_pp_ctrl1_wr_s,
		ext_drop_cnt_wr_o => ext_drop_cnt_wr_s,

		ext_pb_ctrl1_i => ext_pb_ctrl1_s,
		ext_pb_ctrl2_i => ext_pb_ctrl2_s,
		ext_pb_ctrl3_i => ext_pb_ctrl3_s,
		ext_pb_ctrl4_i => ext_pb_ctrl4_s,

		ext_pp_ctrl1_i => ext_pp_ctrl1_s,
		ext_pp_ctrl2_i => ext_pp_ctrl2_s,
		ext_pp_ctrl3_i => ext_pp_ctrl3_s,

		ext_drop_cnt_i => ext_drop_cnt_s,

		S_AXI_ACLK => S_AXI_ACLK,	
		S_AXI_ARESETN => S_AXI_ARESETN,	

		S_AXI_AWADDR => S_AXI_AWADDR,	
		-- S_AXI_AWLEN => S_AXI_AWLEN,	
		-- S_AXI_AWSIZE => S_AXI_AWSIZE,	
		-- S_AXI_AWBURST => S_AXI_AWBURST,	
		S_AXI_AWVALID => S_AXI_AWVALID,	
		S_AXI_AWREADY => S_AXI_AWREADY,	
    
		S_AXI_WDATA => S_AXI_WDATA,	
		S_AXI_WSTRB => S_AXI_WSTRB,	
		-- S_AXI_WLAST => S_AXI_WLAST,	
		S_AXI_WVALID => S_AXI_WVALID,	
		S_AXI_WREADY => S_AXI_WREADY,	

		S_AXI_BRESP => S_AXI_BRESP,	
		S_AXI_BVALID => S_AXI_BVALID,	
		S_AXI_BREADY => S_AXI_BREADY,	

		S_AXI_ARADDR => S_AXI_ARADDR,	
		-- S_AXI_ARLEN => S_AXI_ARLEN,	
		-- S_AXI_ARSIZE => S_AXI_ARSIZE,	
		-- S_AXI_ARBURST => S_AXI_ARBURST,	
		S_AXI_ARVALID => S_AXI_ARVALID,	
		S_AXI_ARREADY => S_AXI_ARREADY,	

		S_AXI_RDATA => S_AXI_RDATA,	
		S_AXI_RRESP => S_AXI_RRESP,	
		-- S_AXI_RLAST => S_AXI_RLAST,	
		S_AXI_RVALID => S_AXI_RVALID,	
		S_AXI_RREADY => S_AXI_RREADY
  );

end architecture;