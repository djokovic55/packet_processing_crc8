library ieee;
  use ieee.std_logic_1164.all;
  use ieee.numeric_std.all;

entity regs is
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
		int_irq_o : out std_logic_vector(2 downto 0);

		-- [x] interface with builder0

		pb0_start_o : out std_logic;
		pb0_start_top : out std_logic;
		pb0_busy_i : in std_logic;
		pb0_busy_top : out std_logic;
		pb0_irq_i : in std_logic;
		pb0_irq_top : out std_logic;
		pb0_addr_in_o : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		pb0_addr_in_top : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		pb0_byte_cnt_o : out std_logic_vector(3 downto 0);
		pb0_byte_cnt_top : out std_logic_vector(3 downto 0);
		pb0_pkt_type_o : out std_logic_vector(3 downto 0);
		pb0_pkt_type_top : out std_logic_vector(3 downto 0);
		pb0_ecc_en_o : out std_logic;
		pb0_ecc_en_top : out std_logic;
		pb0_crc_en_o : out std_logic;
		pb0_crc_en_top : out std_logic;
		pb0_ins_ecc_err_o : out std_logic_vector(1 downto 0);
		pb0_ins_ecc_err_top : out std_logic_vector(1 downto 0);
		pb0_ins_crc_err_o : out std_logic;
		pb0_ins_crc_err_top : out std_logic;
		pb0_ecc_val_o : out std_logic_vector(3 downto 0);
		pb0_ecc_val_top : out std_logic_vector(3 downto 0);
		pb0_crc_val_o: out std_logic_vector(7 downto 0);
		pb0_crc_val_top: out std_logic_vector(7 downto 0);
		pb0_sop_val_o: out std_logic_vector(2 downto 0);
		pb0_sop_val_top: out std_logic_vector(2 downto 0);
		pb0_data_sel_o: out std_logic_vector(3 downto 0);
		pb0_data_sel_top: out std_logic_vector(3 downto 0);
		pb0_addr_out_o: out std_logic_vector(31 downto 0);
		pb0_addr_out_top: out std_logic_vector(31 downto 0);

		-- [x] interface with builder1
		pb1_start_o : out std_logic;
		pb1_start_top : out std_logic;
		pb1_busy_i : in std_logic;
		pb1_busy_top : out std_logic;
		pb1_irq_i : in std_logic;
		pb1_irq_top : out std_logic;
		pb1_addr_in_o : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		pb1_addr_in_top : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		pb1_byte_cnt_o : out std_logic_vector(3 downto 0);
		pb1_byte_cnt_top : out std_logic_vector(3 downto 0);
		pb1_pkt_type_o : out std_logic_vector(3 downto 0);
		pb1_pkt_type_top : out std_logic_vector(3 downto 0);
		pb1_ecc_en_o : out std_logic;
		pb1_ecc_en_top : out std_logic;
		pb1_crc_en_o : out std_logic;
		pb1_crc_en_top : out std_logic;
		pb1_ins_ecc_err_o : out std_logic_vector(1 downto 0);
		pb1_ins_ecc_err_top : out std_logic_vector(1 downto 0);
		pb1_ins_crc_err_o : out std_logic;
		pb1_ins_crc_err_top : out std_logic;
		pb1_ecc_val_o : out std_logic_vector(3 downto 0);
		pb1_ecc_val_top : out std_logic_vector(3 downto 0);
		pb1_crc_val_o: out std_logic_vector(7 downto 0);
		pb1_crc_val_top: out std_logic_vector(7 downto 0);
		pb1_sop_val_o: out std_logic_vector(2 downto 0);
		pb1_sop_val_top: out std_logic_vector(2 downto 0);
		pb1_data_sel_o: out std_logic_vector(3 downto 0);
		pb1_data_sel_top: out std_logic_vector(3 downto 0);
		pb1_addr_out_o: out std_logic_vector(31 downto 0);
		pb1_addr_out_top: out std_logic_vector(31 downto 0);
		-- [x] interface with parser

		pp_start_o : out std_logic;
		pp_start_top : out std_logic;
		pp_busy_i : in std_logic;
		pp_busy_top : out std_logic;
		pp_irq_i : in std_logic;
		pp_irq_top : out std_logic;
		pp_addr_hdr_o : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		pp_addr_hdr_top : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		pp_ignore_ecc_err_o : out std_logic;
		pp_ignore_ecc_err_top : out std_logic;
		pp_pkt_ecc_corr_i : in std_logic;
		pp_pkt_ecc_corr_top : out std_logic;
		pp_pkt_ecc_uncorr_i : in std_logic;
		pp_pkt_ecc_uncorr_top : out std_logic;
		pp_pkt_crc_err_i : in std_logic;
		pp_pkt_crc_err_top : out std_logic;
		pp_pkt_byte_cnt_i : in std_logic_vector(3 downto 0);
		pp_pkt_byte_cnt_top : out std_logic_vector(3 downto 0);
		pp_pkt_type_i : in std_logic_vector(3 downto 0);
		pp_pkt_type_top : out std_logic_vector(3 downto 0);

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

architecture implementation of regs is
  component slave_axi_lite_regs_cont is
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
		-- ADDR_O : out std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		-- DATA_O : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
		-- WR_O : out std_logic;

		-- DATA_I : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);

		reg_data_o : out std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);

		sys_cfg_wr_o : out std_logic; -- irq_line_0
		sys_cfg_i : in std_logic_vector(2 downto 0); -- irq_line_0

		----------------------------------------------------------------------------------------- 
		-- PB0 regs
		----------------------------------------------------------------------------------------- 
		pb0_sts_i : in std_logic;

		pb0_ctrl0_wr_o : out std_logic; 
		pb0_ctrl0_i : in std_logic; 

		pb0_ctrl1_wr_o : out std_logic; 
		pb0_ctrl1_i : in std_logic; 

		-- byte access
		pb0_ctrl2_wr_o : out std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
		pb0_ctrl2_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 
		
		-- byte access
		pb0_ctrl3_wr_o : out std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
		pb0_ctrl3_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 

		-- byte access
		pb0_ctrl4_wr_o : out std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
		pb0_ctrl4_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 

		----------------------------------------------------------------------------------------- 
		-- PB1 regs
		----------------------------------------------------------------------------------------- 
		pb1_sts_i : in std_logic;

		pb1_ctrl0_wr_o : out std_logic; 
		pb1_ctrl0_i : in std_logic; 

		pb1_ctrl1_wr_o : out std_logic; 
		pb1_ctrl1_i : in std_logic; 

		-- byte access
		pb1_ctrl2_wr_o : out std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
		pb1_ctrl2_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 
		
		-- byte access
		pb1_ctrl3_wr_o : out std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
		pb1_ctrl3_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 

		-- byte access
		pb1_ctrl4_wr_o : out std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
		pb1_ctrl4_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 

		----------------------------------------------------------------------------------------- 
		-- PP regs
		----------------------------------------------------------------------------------------- 

		pp_sts_i : in std_logic_vector(11 downto 0);

		pp_ctrl0_wr_o : out std_logic; 
		pp_ctrl0_i : in std_logic; 

		pp_ctrl1_wr_o : out std_logic; 
		pp_ctrl1_i : in std_logic; 

		-- byte access
		pp_ctrl2_wr_o : out std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
		pp_ctrl2_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 
		
		pp_ctrl3_wr_o : out std_logic; 
		pp_ctrl3_i : in std_logic; 
		----------------------------------------------------------------------------------------- 
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
  
  signal reg_data_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);

	signal sys_cfg_wr_s : std_logic; -- irq_line_0
	signal sys_cfg_s : std_logic_vector(2 downto 0); -- irq_line_0

  ----------------------------------------------------------------------------------------- 
  -- PB0 regs
  ----------------------------------------------------------------------------------------- 
	signal pb0_sts_s : std_logic; -- RO
	signal pb0_sts_conf : std_logic; -- RO

	signal pb0_ctrl0_wr_s : std_logic; 
	signal pb0_ctrl0_s : std_logic; 

	signal pb0_ctrl1_wr_s : std_logic; 
	signal pb0_ctrl1_s : std_logic; 
	signal pb0_ctrl1_conf : std_logic; 

  -- byte access
	signal pb0_ctrl2_wr_s : std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
	signal pb0_ctrl2_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 
  
  -- byte access
	signal pb0_ctrl3_wr_s : std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
	signal pb0_ctrl3_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 

  -- byte access
	signal pb0_ctrl4_wr_s : std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
	signal pb0_ctrl4_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 

  ----------------------------------------------------------------------------------------- 
  -- PB1 regs
  ----------------------------------------------------------------------------------------- 
	signal pb1_sts_s : std_logic; -- RO
	signal pb1_sts_conf : std_logic; -- RO

	signal pb1_ctrl0_wr_s : std_logic; 
	signal pb1_ctrl0_s : std_logic; 

	signal pb1_ctrl1_wr_s : std_logic; 
	signal pb1_ctrl1_s : std_logic; 
	signal pb1_ctrl1_conf : std_logic; 

  -- byte access
	signal pb1_ctrl2_wr_s : std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
	signal pb1_ctrl2_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 
  
  -- byte access
	signal pb1_ctrl3_wr_s : std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
	signal pb1_ctrl3_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 

  -- byte access
	signal pb1_ctrl4_wr_s : std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
	signal pb1_ctrl4_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 

  ----------------------------------------------------------------------------------------- 
  -- PP regs
  ----------------------------------------------------------------------------------------- 

	signal pp_sts_s : std_logic_vector(11 downto 0); -- RO
	signal pp_sts_conf : std_logic_vector(11 downto 0); -- RO

	signal pp_ctrl0_wr_s : std_logic; 
	signal pp_ctrl0_s : std_logic; 

	signal pp_ctrl1_wr_s : std_logic; 
	signal pp_ctrl1_s : std_logic; 
	signal pp_ctrl1_conf : std_logic; 

  -- byte access
	signal pp_ctrl2_wr_s : std_logic_vector((C_S_AXI_DATA_WIDTH/8)-1 downto 0); 
	signal pp_ctrl2_s : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); 
  
	signal pp_ctrl3_wr_s : std_logic; 
	signal pp_ctrl3_s : std_logic; 
  ----------------------------------------------------------------------------------------- 
	
begin

  -- [x] slave AXI cont added
  -- [x] AXI cont update to lite version
  -- [x] regs implementation
  -- [ ] top integration 
  --------------------------------------------------------------------------------	
  -- I/O connections controller - regs, internal irqs
  --------------------------------------------------------------------------------	
	-- NOT_IN_SPEC, irq signals directly forwarded from builder blocks
	int_irq_o(0) <= pb0_irq_i;
	int_irq_o(1) <= pb1_irq_i;
	int_irq_o(2) <= pp_ctrl1_s;

	--------------------------------------------------------------------------------	
	-- I/O connections PB0 and top assignments
	--------------------------------------------------------------------------------	
	-- NOT_IN_SPEC, irq signals directly forwarded from builder blocks
	pb0_irq_top <= pb0_irq_i;
	pb0_busy_top <= pb0_busy_i; 

	pb0_start_o <= pb0_ctrl0_s; 
	pb0_start_top <= pb0_ctrl0_s; 
	-- IMPORTANT all inputs to register are assinged inside corresponding proccesses
	-- pb0_sts_s <= pb0_busy_i; 
	-- FIXME Interrupt req is not implemented fully because cont does not have connections with controller
	-- done 
	-- pb0_ctrl1_s <= pb0_irq_i; 

	pb0_addr_in_o <= pb0_ctrl2_s; 
	pb0_addr_in_top <= pb0_ctrl2_s; 
  
  -- ctr3 confing
	pb0_byte_cnt_o <= pb0_ctrl3_s(3 downto 0); -- 4 
	pb0_byte_cnt_top <= pb0_ctrl3_s(3 downto 0); -- 4 
	pb0_pkt_type_o <= pb0_ctrl3_s(7 downto 4); -- 4
	pb0_pkt_type_top <= pb0_ctrl3_s(7 downto 4); -- 4
	pb0_ecc_en_o <= pb0_ctrl3_s(8); -- 1
	pb0_ecc_en_top <= pb0_ctrl3_s(8); -- 1
	pb0_crc_en_o <= pb0_ctrl3_s(9); -- 1
	pb0_crc_en_top <= pb0_ctrl3_s(9); -- 1
	pb0_ins_ecc_err_o <= pb0_ctrl3_s(11 downto 10); -- 2
	pb0_ins_ecc_err_top <= pb0_ctrl3_s(11 downto 10); -- 2
	pb0_ins_crc_err_o <= pb0_ctrl3_s(12); -- 1
	pb0_ins_crc_err_top <= pb0_ctrl3_s(12); -- 1
	pb0_ecc_val_o <= pb0_ctrl3_s(16 downto 13); -- 4
	pb0_ecc_val_top <= pb0_ctrl3_s(16 downto 13); -- 4
	pb0_crc_val_o <= pb0_ctrl3_s(24 downto 17); -- 8
	pb0_crc_val_top <= pb0_ctrl3_s(24 downto 17); -- 8
	pb0_sop_val_o <= pb0_ctrl3_s(27 downto 25); -- 3
	pb0_sop_val_top <= pb0_ctrl3_s(27 downto 25); -- 3
	pb0_data_sel_o <= pb0_ctrl3_s(31 downto 28); -- 4
	pb0_data_sel_top <= pb0_ctrl3_s(31 downto 28); -- 4

  -- byte access
	pb0_addr_out_o <= pb0_ctrl4_s; 
	pb0_addr_out_top <= pb0_ctrl4_s; 
	
	--------------------------------------------------------------------------------	
	-- I/O connections PB1 and top assignments
	--------------------------------------------------------------------------------	
	-- NOT_IN_SPEC, irq signals directly forwarded from builder blocks
	pb1_irq_top <= pb1_irq_i;
	pb1_busy_top <= pb1_busy_i; 

	pb1_start_o <= pb1_ctrl0_s; 
	pb1_start_top <= pb1_ctrl0_s; 
	-- pb1_sts_s <= pb1_busy_i; 
	--FIXME Interrupt req is not implemented fully because cont does not have connections with regs
	-- pb1_ctrl1_s <= pb1_irq_i; 

	pb1_addr_in_o <= pb1_ctrl2_s; 
	pb1_addr_in_top <= pb1_ctrl2_s; 
  
  -- ctr3 confing
	pb1_byte_cnt_o <= pb1_ctrl3_s(3 downto 0); 
	pb1_byte_cnt_top <= pb1_ctrl3_s(3 downto 0); 
	pb1_pkt_type_o <= pb1_ctrl3_s(7 downto 4); 
	pb1_pkt_type_top <= pb1_ctrl3_s(7 downto 4); 
	pb1_ecc_en_o <= pb1_ctrl3_s(8); 
	pb1_ecc_en_top <= pb1_ctrl3_s(8); 
	pb1_crc_en_o <= pb1_ctrl3_s(9); 
	pb1_crc_en_top <= pb1_ctrl3_s(9); 
	pb1_ins_ecc_err_o <= pb1_ctrl3_s(11 downto 10); 
	pb1_ins_ecc_err_top <= pb1_ctrl3_s(11 downto 10); 
	pb1_ins_crc_err_o <= pb1_ctrl3_s(12); 
	pb1_ins_crc_err_top <= pb1_ctrl3_s(12); 
	pb1_ecc_val_o <= pb1_ctrl3_s(16 downto 13); 
	pb1_ecc_val_top <= pb1_ctrl3_s(16 downto 13); 
	pb1_crc_val_o <= pb1_ctrl3_s(24 downto 17); 
	pb1_crc_val_top <= pb1_ctrl3_s(24 downto 17); 
	pb1_sop_val_o <= pb1_ctrl3_s(27 downto 25); 
	pb1_sop_val_top <= pb1_ctrl3_s(27 downto 25); 
	pb1_data_sel_o <= pb1_ctrl3_s(31 downto 28); 
	pb1_data_sel_top <= pb1_ctrl3_s(31 downto 28); 

  -- byte access
	pb1_addr_out_o <= pb1_ctrl4_s; 
	pb1_addr_out_top <= pb1_ctrl4_s; 

	--------------------------------------------------------------------------------	
	-- I/O connections PP
	--------------------------------------------------------------------------------	
	

	-- pp_sts_s(0) <= pp_busy_i;
	-- pp_sts_s(1) <= pp_pkt_ecc_corr_i;
	-- pp_sts_s(2) <= pp_pkt_ecc_uncorr_i;
	-- pp_sts_s(3) <= pp_pkt_crc_err_i;
	-- pp_sts_s(7 downto 4) <= pp_pkt_byte_cnt_i;
	-- pp_sts_s(11 downto 8) <= pp_pkt_type_i;

	pp_start_o <= pp_ctrl0_s; 
	pp_start_top <= pp_ctrl0_s; 


	-- pp_ctrl1_s <= pp_irq_i; 

	pp_addr_hdr_o <= pp_ctrl2_s; 
	pp_addr_hdr_top <= pp_ctrl2_s; 
	pp_ignore_ecc_err_o <= pp_ctrl3_s; 
	pp_ignore_ecc_err_top <= pp_ctrl3_s; 

	-- BUG irq directly forwarded on top whereas reg value goes to main cont
	-- pass reg value insted
	pp_irq_top <= pp_ctrl1_s; 

	pp_busy_top <= pp_busy_i;
	pp_pkt_ecc_corr_top <= pp_pkt_ecc_corr_i;
	pp_pkt_ecc_uncorr_top <= pp_pkt_ecc_uncorr_i;
	pp_pkt_crc_err_top <= pp_pkt_crc_err_i;
	pp_pkt_byte_cnt_top <= pp_pkt_byte_cnt_i;
	pp_pkt_type_top <= pp_pkt_type_i;
	--------------------------------------------------------------------------------	
	-- Regs
	--------------------------------------------------------------------------------	
	-- RW
	sys_cfg: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				sys_cfg_s <= (others => '0');
			elsif sys_cfg_wr_s = '1' then
				sys_cfg_s <= reg_data_s(2 downto 0);
			end if;
		end if;
	end process;


	-- RO
	pb0_sts: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb0_sts_s <= '0';
			else
				pb0_sts_s <= pb0_busy_i;
			end if;
		end if;
	end process;

	-- RW start reg
	pb0_ctrl0: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb0_ctrl0_s <= '0';
			elsif pb0_ctrl0_wr_s = '1' then
				pb0_ctrl0_s <= reg_data_s(0);
			else
				pb0_ctrl0_s <= '0'; -- negate to generate pulse
			end if;
		end if;
	end process;

	-- W1C
	pb0_ctrl1: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb0_ctrl1_s <= '0';
			elsif pb0_ctrl1_wr_s = '1' then
				if(reg_data_s(0) = '1') then
					pb0_ctrl1_s <= '0';
				end if;
			elsif(pb0_irq_i = '1') then 
				pb0_ctrl1_s <= '1';
			-- added logic to solve controller irq reset bug, not in spec
			else
				pb0_ctrl1_s <= '0';
			end if;
		end if;
	end process;

	-- RW 
	pb0_ctrl2: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb0_ctrl2_s <= (others => '0');
			else
				if pb0_ctrl2_wr_s(3) = '1' then
					pb0_ctrl2_s(31 downto 24) <= reg_data_s(31 downto 24);
				end if;
				if pb0_ctrl2_wr_s(2) = '1' then
					pb0_ctrl2_s(23 downto 16) <= reg_data_s(23 downto 16);
				end if;
				if pb0_ctrl2_wr_s(1) = '1' then
					pb0_ctrl2_s(15 downto 8) <= reg_data_s(15 downto 8);
				end if;
				if pb0_ctrl2_wr_s(0) = '1' then
					pb0_ctrl2_s(7 downto 0) <= reg_data_s(7 downto 0);
				end if;
			end if;
		end if;
	end process;


	-- RW 
	pb0_ctrl3: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb0_ctrl3_s <= (others => '0');
			else
				if pb0_ctrl3_wr_s(3) = '1' then
					pb0_ctrl3_s(31 downto 24) <= reg_data_s(31 downto 24);
				end if;
				if pb0_ctrl3_wr_s(2) = '1' then
					pb0_ctrl3_s(23 downto 16) <= reg_data_s(23 downto 16);
				end if;
				if pb0_ctrl3_wr_s(1) = '1' then
					pb0_ctrl3_s(15 downto 8) <= reg_data_s(15 downto 8);
				end if;
				if pb0_ctrl3_wr_s(0) = '1' then
					pb0_ctrl3_s(7 downto 0) <= reg_data_s(7 downto 0);
				end if;
			end if;
		end if;
	end process;


	-- RW 
	pb0_ctrl4: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb0_ctrl4_s <= (others => '0');
			else
				if pb0_ctrl4_wr_s(3) = '1' then
					pb0_ctrl4_s(31 downto 24) <= reg_data_s(31 downto 24);
				end if;
				if pb0_ctrl4_wr_s(2) = '1' then
					pb0_ctrl4_s(23 downto 16) <= reg_data_s(23 downto 16);
				end if;
				if pb0_ctrl4_wr_s(1) = '1' then
					pb0_ctrl4_s(15 downto 8) <= reg_data_s(15 downto 8);
				end if;
				if pb0_ctrl4_wr_s(0) = '1' then
					pb0_ctrl4_s(7 downto 0) <= reg_data_s(7 downto 0);
				end if;
			end if;
		end if;
	end process;
  ----------------------------------------------------------------------------------------- 

	-- RO 
	pb1_sts: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb1_sts_s <= '0';
			else
				pb1_sts_s <= pb1_busy_i;
			end if;
		end if;
	end process;

	-- RW start reg
	pb1_ctrl0: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb1_ctrl0_s <= '0';
			elsif pb1_ctrl0_wr_s = '1' then
				pb1_ctrl0_s <= reg_data_s(0);
			else
				pb1_ctrl0_s <= '0'; -- negate to generate pulse

			end if;
		end if;
	end process;

	-- W1C
	pb1_ctrl1: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb1_ctrl1_s <= '0';
			elsif pb1_ctrl1_wr_s = '1' then
				if(reg_data_s(0) = '1') then
					pb1_ctrl1_s <= '0';
				end if;
			elsif(pb1_irq_i = '1') then 
				pb1_ctrl1_s <= '1';
			-- added logic to solve controller irq reset bug, not in spec
			else
				pb1_ctrl1_s <= '0';
			end if;
		end if;
	end process;

	-- RW 
	pb1_ctrl2: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb1_ctrl2_s <= (others => '0');
			else
				if pb1_ctrl2_wr_s(3) = '1' then
					pb1_ctrl2_s(31 downto 24) <= reg_data_s(31 downto 24);
				end if;
				if pb1_ctrl2_wr_s(2) = '1' then
					pb1_ctrl2_s(23 downto 16) <= reg_data_s(23 downto 16);
				end if;
				if pb1_ctrl2_wr_s(1) = '1' then
					pb1_ctrl2_s(15 downto 8) <= reg_data_s(15 downto 8);
				end if;
				if pb1_ctrl2_wr_s(0) = '1' then
					pb1_ctrl2_s(7 downto 0) <= reg_data_s(7 downto 0);
				end if;
			end if;
		end if;
	end process;


	-- RW 
	pb1_ctrl3: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb1_ctrl3_s <= (others => '0');
			else
				if pb1_ctrl3_wr_s(3) = '1' then
					pb1_ctrl3_s(31 downto 24) <= reg_data_s(31 downto 24);
				end if;
				if pb1_ctrl3_wr_s(2) = '1' then
					pb1_ctrl3_s(23 downto 16) <= reg_data_s(23 downto 16);
				end if;
				if pb1_ctrl3_wr_s(1) = '1' then
					pb1_ctrl3_s(15 downto 8) <= reg_data_s(15 downto 8);
				end if;
				if pb1_ctrl3_wr_s(0) = '1' then
					pb1_ctrl3_s(7 downto 0) <= reg_data_s(7 downto 0);
				end if;
			end if;
		end if;
	end process;


	-- RW 
	pb1_ctrl4: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pb1_ctrl4_s <= (others => '0');
			else
				if pb1_ctrl4_wr_s(3) = '1' then
					pb1_ctrl4_s(31 downto 24) <= reg_data_s(31 downto 24);
				end if;
				if pb1_ctrl4_wr_s(2) = '1' then
					pb1_ctrl4_s(23 downto 16) <= reg_data_s(23 downto 16);
				end if;
				if pb1_ctrl4_wr_s(1) = '1' then
					pb1_ctrl4_s(15 downto 8) <= reg_data_s(15 downto 8);
				end if;
				if pb1_ctrl4_wr_s(0) = '1' then
					pb1_ctrl4_s(7 downto 0) <= reg_data_s(7 downto 0);
				end if;
			end if;
		end if;
	end process;
  ----------------------------------------------------------------------------------------- 

	-- RO 
	pp_sts: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pp_sts_s <= (others => '0');
			else
				pp_sts_s(0) <= pp_busy_i;
				pp_sts_s(1) <= pp_pkt_ecc_corr_i;
				pp_sts_s(2) <= pp_pkt_ecc_uncorr_i;
				pp_sts_s(3) <= pp_pkt_crc_err_i;
				pp_sts_s(7 downto 4) <= pp_pkt_byte_cnt_i;
				pp_sts_s(11 downto 8) <= pp_pkt_type_i;
			end if;
		end if;
	end process;

	-- RW start reg
	pp_ctrl0: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pp_ctrl0_s <= '0';
			elsif pp_ctrl0_wr_s = '1' then
				pp_ctrl0_s <= reg_data_s(0);
			else
				pp_ctrl0_s <= '0'; -- negate to generate pulse
			end if;
		end if;
	end process;

	-- W1C 
	pp_ctrl1: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pp_ctrl1_s <= '0';
			elsif pp_ctrl1_wr_s = '1' then
				if(reg_data_s(0) = '1') then
					pp_ctrl1_s <= '0';
				end if;
			elsif(pp_irq_i = '1') then 
				pp_ctrl1_s <= '1'; 
			end if;
		end if;
	end process;

	-- RW 
	pp_ctrl2: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pp_ctrl2_s <= (others => '0');
			else
				if pp_ctrl2_wr_s(3) = '1' then
					pp_ctrl2_s(31 downto 24) <= reg_data_s(31 downto 24);
				end if;
				if pp_ctrl2_wr_s(2) = '1' then
					pp_ctrl2_s(23 downto 16) <= reg_data_s(23 downto 16);
				end if;
				if pp_ctrl2_wr_s(1) = '1' then
					pp_ctrl2_s(15 downto 8) <= reg_data_s(15 downto 8);
				end if;
				if pp_ctrl2_wr_s(0) = '1' then
					pp_ctrl2_s(7 downto 0) <= reg_data_s(7 downto 0);
				end if;
			end if;
		end if;
	end process;


	-- RW 
	pp_ctrl3: process(S_AXI_ACLK)
  begin
		if S_AXI_ACLK'event and S_AXI_ACLK = '1' then
			if S_AXI_ARESETN = '1' then
				pp_ctrl3_s <= '0';
			elsif pp_ctrl3_wr_s = '1' then
				pp_ctrl3_s <= reg_data_s(0);
			end if;
		end if;
	end process;


  regs_cont: slave_axi_lite_regs_cont
  generic map(

		C_S_AXI_DATA_WIDTH => C_S_AXI_DATA_WIDTH,	
		C_S_AXI_ADDR_WIDTH => C_S_AXI_ADDR_WIDTH	
  )
  port map(

		reg_data_o => reg_data_s,

		sys_cfg_wr_o => sys_cfg_wr_s, 
		sys_cfg_i => sys_cfg_s, 

		----------------------------------------------------------------------------------------- 
		-- PB0 regs
		----------------------------------------------------------------------------------------- 
		pb0_sts_i => pb0_sts_s,

		pb0_ctrl0_wr_o => pb0_ctrl0_wr_s, 
		pb0_ctrl0_i => pb0_ctrl0_s, 

		pb0_ctrl1_wr_o => pb0_ctrl1_wr_s, 
		pb0_ctrl1_i => pb0_ctrl1_s, 

		-- byte access
		pb0_ctrl2_wr_o => pb0_ctrl2_wr_s, 
		pb0_ctrl2_i => pb0_ctrl2_s, 
		
		-- byte access
		pb0_ctrl3_wr_o => pb0_ctrl3_wr_s, 
		pb0_ctrl3_i => pb0_ctrl3_s, 

		-- byte access
		pb0_ctrl4_wr_o => pb0_ctrl4_wr_s, 
		pb0_ctrl4_i => pb0_ctrl4_s, 

		----------------------------------------------------------------------------------------- 
		-- PB1 regs
		----------------------------------------------------------------------------------------- 
		pb1_sts_i => pb1_sts_s,

		pb1_ctrl0_wr_o => pb1_ctrl0_wr_s, 
		pb1_ctrl0_i => pb1_ctrl0_s, 

		pb1_ctrl1_wr_o => pb1_ctrl1_wr_s, 
		pb1_ctrl1_i => pb1_ctrl1_s, 

		-- byte access
		pb1_ctrl2_wr_o => pb1_ctrl2_wr_s, 
		pb1_ctrl2_i => pb1_ctrl2_s, 
		
		-- byte access
		pb1_ctrl3_wr_o => pb1_ctrl3_wr_s, 
		pb1_ctrl3_i => pb1_ctrl3_s, 

		-- byte access
		pb1_ctrl4_wr_o => pb1_ctrl4_wr_s, 
		pb1_ctrl4_i => pb1_ctrl4_s, 

		----------------------------------------------------------------------------------------- 
		-- PP regs
		----------------------------------------------------------------------------------------- 

		pp_sts_i => pp_sts_s,

		pp_ctrl0_wr_o => pp_ctrl0_wr_s, 
		pp_ctrl0_i => pp_ctrl0_s, 

		pp_ctrl1_wr_o => pp_ctrl1_wr_s, 
		pp_ctrl1_i => pp_ctrl1_s, 

		-- byte access
		pp_ctrl2_wr_o => pp_ctrl2_wr_s, 
		pp_ctrl2_i => pp_ctrl2_s, 
		
		pp_ctrl3_wr_o => pp_ctrl3_wr_s, 
		pp_ctrl3_i => pp_ctrl3_s, 
		----------------------------------------------------------------------------------------- 

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
