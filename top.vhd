library ieee;
  use ieee.std_logic_1164.all;
  use ieee.numeric_std.all;

entity top is
  generic (
    DATA_WIDTH : integer := 32;
    ADDR_WIDTH : integer := 32;
    BURST_LEN : integer := 16
  );
  port (
        clk : in std_logic;
        reset : in std_logic;
        --------------------------------------------------------------------------------
        -- CONTROLLER
        --------------------------------------------------------------------------------
        AXI_BASE_ADDRESS_I_CTRL  : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- base address    
        --  WRITE CHANNEL
        AXI_WRITE_ADDRESS_I_CTRL : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- address added
                                            -- to base address
        AXI_WRITE_INIT_I_CTRL    : in  std_logic;  -- start write transactions    
        AXI_WRITE_DATA_I_CTRL    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        AXI_WRITE_VLD_I_CTRL     : in  std_logic;  --  indicates that write data is valid
        AXI_WRITE_RDY_O_CTRL     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
        AXI_WRITE_DONE_O_CTRL    : out std_logic;  -- indicates that burst has finished
        -- READ CHANNEL

        AXI_READ_ADDRESS_I_CTRL : in std_logic_vector(ADDR_WIDTH-1 downto 0);  -- address added
                                                                -- to base address

        AXI_READ_INIT_I_CTRL : in  std_logic;    --starts read transaction
        AXI_READ_DATA_O_CTRL : out std_logic_vector(DATA_WIDTH-1 downto 0);  -- data read from                                                             -- ddr
        AXI_READ_VLD_O_CTRL  : out std_logic;    -- axi_read_data_o is valid
        AXI_READ_RDY_I_CTRL  : in std_logic;    -- axi_read_data_o is valid
        axi_read_last_o_ctrl : out std_logic;    -- axi_read_data_o is valid
        --------------------------------------------------------------------------------
        -- PB1
        --------------------------------------------------------------------------------
        AXI_BASE_ADDRESS_I_PB0  : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- base address    
        --  WRITE CHANNEL
        AXI_WRITE_ADDRESS_I_PB0 : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- address added
                                            -- to base address
        AXI_WRITE_INIT_I_PB0    : in  std_logic;  -- start write transactions    
        AXI_WRITE_DATA_I_PB0    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        AXI_WRITE_VLD_I_PB0     : in  std_logic;  --  indicates that write data is valid
        AXI_WRITE_RDY_O_PB0     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
        AXI_WRITE_DONE_O_PB0    : out std_logic;  -- indicates that burst has finished
        -- READ CHANNEL

        AXI_READ_ADDRESS_I_PB0 : in std_logic_vector(ADDR_WIDTH-1 downto 0);  -- address added
                                                                -- to base address

        AXI_READ_INIT_I_PB0 : in  std_logic;    --starts read transaction
        AXI_READ_DATA_O_PB0 : out std_logic_vector(DATA_WIDTH-1 downto 0);  -- data read from                                                             -- ddr
        AXI_READ_VLD_O_PB0  : out std_logic;    -- axi_read_data_o is valid
        AXI_READ_RDY_I_PB0  : in std_logic;    -- axi_read_data_o is valid
        AXI_READ_LAST_O_PB0 : out std_logic;    -- axi_read_data_o is valid

        --------------------------------------------------------------------------------
        -- PB2
        --------------------------------------------------------------------------------
        AXI_BASE_ADDRESS_I_PB1  : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- base address    
        --  WRITE CHANNEL
        AXI_WRITE_ADDRESS_I_PB1 : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- address added
                                            -- to base address
        AXI_WRITE_INIT_I_PB1    : in  std_logic;  -- start write transactions    
        AXI_WRITE_DATA_I_PB1    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        AXI_WRITE_VLD_I_PB1     : in  std_logic;  --  indicates that write data is valid
        AXI_WRITE_RDY_O_PB1     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
        AXI_WRITE_DONE_O_PB1    : out std_logic;  -- indicates that burst has finished
        -- READ CHANNEL

        AXI_READ_ADDRESS_I_PB1 : in std_logic_vector(ADDR_WIDTH-1 downto 0);  -- address added
                                                                -- to base address

        AXI_READ_INIT_I_PB1 : in  std_logic;    --starts read transaction
        AXI_READ_DATA_O_PB1 : out std_logic_vector(DATA_WIDTH-1 downto 0);  -- data read from                                                             -- ddr
        AXI_READ_VLD_O_PB1  : out std_logic;    -- axi_read_data_o is valid
        AXI_READ_RDY_I_PB1  : in std_logic;    -- axi_read_data_o is valid
        AXI_READ_LAST_O_PB1 : out std_logic;    -- axi_read_data_o is valid

        --------------------------------------------------------------------------------
        -- PP
        --------------------------------------------------------------------------------
        AXI_BASE_ADDRESS_I_PP  : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- base address    
        --  WRITE CHANNEL
        AXI_WRITE_ADDRESS_I_PP : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- address added
                                            -- to base address
        AXI_WRITE_INIT_I_PP    : in  std_logic;  -- start write transactions    
        AXI_WRITE_DATA_I_PP    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        AXI_WRITE_VLD_I_PP     : in  std_logic;  --  indicates that write data is valid
        AXI_WRITE_RDY_O_PP     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
        AXI_WRITE_DONE_O_PP    : out std_logic;  -- indicates that burst has finished
        -- READ CHANNEL

        AXI_READ_ADDRESS_I_PP : in std_logic_vector(ADDR_WIDTH-1 downto 0);  -- address added
                                                                -- to base address

        AXI_READ_INIT_I_PP : in  std_logic;    --starts read transaction
        AXI_READ_DATA_O_PP : out std_logic_vector(DATA_WIDTH-1 downto 0);  -- data read from                                                             -- ddr
        AXI_READ_VLD_O_PP  : out std_logic;    -- axi_read_data_o is valid
        AXI_READ_RDY_I_PP  : in std_logic;    -- axi_read_data_o is valid
	AXI_READ_LAST_O_PP : out std_logic    -- axi_read_data_o is valid
  );
end entity;
-- some test

architecture rtl of top is

  component interconnect is
	generic (
		C_M_AXI_DATA_WIDTH	: integer	:= 32;
		C_M_AXI_ADDR_WIDTH	: integer	:= 32
	);
	port (

		clk	: in std_logic;
		reset	: in std_logic;
		--------------------------------------------------------------------------------
		-- MASTERS
		--------------------------------------------------------------------------------
		-- INTCON PORTS OF CONTROLLER MODULE M1
		--------------------------------------------------------------------------------
			
		-- WRITE ADDRESS CHANNEL
		s_axi_int_awaddr_ctrl: in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		s_axi_int_awlen_ctrl: in std_logic_vector(7 downto 0);
		s_axi_int_awsize_ctrl: in std_logic_vector(2 downto 0);
		s_axi_int_awburst_ctrl: in std_logic_vector(1 downto 0);

		s_axi_int_awvalid_ctrl: in std_logic;
		s_axi_int_awready_ctrl: out std_logic;

		-- WRITE DATA CHANNEL
		s_axi_int_wdata_ctrl: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		s_axi_int_wstrb_ctrl: in std_logic_vector((C_M_AXI_DATA_WIDTH/8)-1 downto 0);
		s_axi_int_wlast_ctrl: in std_logic;

		s_axi_int_wvalid_ctrl: in std_logic;
		s_axi_int_wready_ctrl: out std_logic;

		-- WRITE RESPONSE CHANNEL
		s_axi_int_bresp_ctrl: out std_logic_vector(1 downto 0);

		s_axi_int_bvalid_ctrl: out std_logic;
		s_axi_int_bready_ctrl: in std_logic;

		-- READ ADDRESS CHANNEL
		s_axi_int_araddr_ctrl: in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		s_axi_int_arlen_ctrl: in std_logic_vector(7 downto 0);
		s_axi_int_arsize_ctrl: in std_logic_vector(2 downto 0);
		s_axi_int_arburst_ctrl: in std_logic_vector(1 downto 0);
        
		s_axi_int_arvalid_ctrl: in std_logic;
		s_axi_int_arready_ctrl: out std_logic;

		-- READ DATA CHANNEL
		s_axi_int_rdata_ctrl: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		s_axi_int_rresp_ctrl: out std_logic_vector(1 downto 0);
		s_axi_int_rlast_ctrl: out std_logic;

		s_axi_int_rvalid_ctrl: out std_logic;
		s_axi_int_rready_ctrl: in std_logic;
		--------------------------------------------------------------------------------

		--------------------------------------------------------------------------------
		-- INTCON PORTS OF PACKET BUILDING 0 MODULE M2
		--------------------------------------------------------------------------------
        
		-- WRITE ADDRESS CHANNEL
		s_axi_int_awaddr_pb0: in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		s_axi_int_awlen_pb0: in std_logic_vector(7 downto 0);
		s_axi_int_awsize_pb0: in std_logic_vector(2 downto 0);
		s_axi_int_awburst_pb0: in std_logic_vector(1 downto 0);

		s_axi_int_awvalid_pb0: in std_logic;
		s_axi_int_awready_pb0: out std_logic;

		-- WRITE DATA CHANNEL
		s_axi_int_wdata_pb0: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		s_axi_int_wstrb_pb0: in std_logic_vector((C_M_AXI_DATA_WIDTH/8)-1 downto 0);
		s_axi_int_wlast_pb0: in std_logic;

		s_axi_int_wvalid_pb0: in std_logic;
		s_axi_int_wready_pb0: out std_logic;

		-- WRITE RESPONSE CHANNEL
		s_axi_int_bresp_pb0: out std_logic_vector(1 downto 0);

		s_axi_int_bvalid_pb0: out std_logic;
		s_axi_int_bready_pb0: in std_logic;

		-- READ ADDRESS CHANNEL
		s_axi_int_araddr_pb0: in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		s_axi_int_arlen_pb0: in std_logic_vector(7 downto 0);
		s_axi_int_arsize_pb0: in std_logic_vector(2 downto 0);
		s_axi_int_arburst_pb0: in std_logic_vector(1 downto 0);
        
		s_axi_int_arvalid_pb0: in std_logic;
		s_axi_int_arready_pb0: out std_logic;

        -- READ DATA CHANNEL
		s_axi_int_rdata_pb0: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		s_axi_int_rresp_pb0: out std_logic_vector(1 downto 0);
		s_axi_int_rlast_pb0: out std_logic;

		s_axi_int_rvalid_pb0: out std_logic;
		s_axi_int_rready_pb0: in std_logic;
		--------------------------------------------------------------------------------

		--------------------------------------------------------------------------------
		-- INTCON PORTS OF PACKET BUILDING 1 MODULE M3
		--------------------------------------------------------------------------------
		
		-- WRITE ADDRESS CHANNEL
		s_axi_int_awaddr_pb1: in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		s_axi_int_awlen_pb1: in std_logic_vector(7 downto 0);
		s_axi_int_awsize_pb1: in std_logic_vector(2 downto 0);
		s_axi_int_awburst_pb1: in std_logic_vector(1 downto 0);

		s_axi_int_awvalid_pb1: in std_logic;
		s_axi_int_awready_pb1: out std_logic;

        -- WRITE DATA CHANNEL
		s_axi_int_wdata_pb1: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		s_axi_int_wstrb_pb1: in std_logic_vector((C_M_AXI_DATA_WIDTH/8)-1 downto 0);
		s_axi_int_wlast_pb1: in std_logic;

		s_axi_int_wvalid_pb1: in std_logic;
		s_axi_int_wready_pb1: out std_logic;

        -- WRITE RESPONSE CHANNEL
		s_axi_int_bresp_pb1: out std_logic_vector(1 downto 0);

		s_axi_int_bvalid_pb1: out std_logic;
		s_axi_int_bready_pb1: in std_logic;

        -- READ ADDRESS CHANNEL
		s_axi_int_araddr_pb1: in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		s_axi_int_arlen_pb1: in std_logic_vector(7 downto 0);
		s_axi_int_arsize_pb1: in std_logic_vector(2 downto 0);
		s_axi_int_arburst_pb1: in std_logic_vector(1 downto 0);
        
		s_axi_int_arvalid_pb1: in std_logic;
		s_axi_int_arready_pb1: out std_logic;

        -- READ DATA CHANNEL
		s_axi_int_rdata_pb1: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		s_axi_int_rresp_pb1: out std_logic_vector(1 downto 0);
		s_axi_int_rlast_pb1: out std_logic;

		s_axi_int_rvalid_pb1: out std_logic;
		s_axi_int_rready_pb1: in std_logic;
		--------------------------------------------------------------------------------

		--------------------------------------------------------------------------------
		-- INTCON PORTS OF PACKET PARSING MODULE M4
		--------------------------------------------------------------------------------
		
		-- WRITE ADDRESS CHANNEL
		s_axi_int_awaddr_pp: in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		s_axi_int_awlen_pp: in std_logic_vector(7 downto 0);
		s_axi_int_awsize_pp: in std_logic_vector(2 downto 0);
		s_axi_int_awburst_pp: in std_logic_vector(1 downto 0);

		s_axi_int_awvalid_pp: in std_logic;
		s_axi_int_awready_pp: out std_logic;

        -- WRITE DATA CHANNEL
		s_axi_int_wdata_pp: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		s_axi_int_wstrb_pp: in std_logic_vector((C_M_AXI_DATA_WIDTH/8)-1 downto 0);
		s_axi_int_wlast_pp: in std_logic;

		s_axi_int_wvalid_pp: in std_logic;
		s_axi_int_wready_pp: out std_logic;

        -- WRITE RESPONSE CHANNEL
		s_axi_int_bresp_pp: out std_logic_vector(1 downto 0);

		s_axi_int_bvalid_pp: out std_logic;
		s_axi_int_bready_pp: in std_logic;

        -- READ ADDRESS CHANNEL
		s_axi_int_araddr_pp: in std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		s_axi_int_arlen_pp: in std_logic_vector(7 downto 0);
		s_axi_int_arsize_pp: in std_logic_vector(2 downto 0);
		s_axi_int_arburst_pp: in std_logic_vector(1 downto 0);
        
		s_axi_int_arvalid_pp: in std_logic;
		s_axi_int_arready_pp: out std_logic;

        -- READ DATA CHANNEL
		s_axi_int_rdata_pp: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		s_axi_int_rresp_pp: out std_logic_vector(1 downto 0);
		s_axi_int_rlast_pp: out std_logic;

		s_axi_int_rvalid_pp: out std_logic;
		s_axi_int_rready_pp: in std_logic;
		--------------------------------------------------------------------------------

		--------------------------------------------------------------------------------
		-- SLAVES
		--------------------------------------------------------------------------------
		-- INTCON PORTS OF INCOMING MEMORY MODULE S1
		--------------------------------------------------------------------------------

        -- ADDRESS WRITE CHANNEL
		m_axi_int_awaddr_inmem: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		m_axi_int_awlen_inmem: out std_logic_vector(7 downto 0);
		m_axi_int_awsize_inmem: out std_logic_vector(2 downto 0);
		m_axi_int_awburst_inmem: out std_logic_vector(1 downto 0);

		m_axi_int_awvalid_inmem: out std_logic;
		m_axi_int_awready_inmem: in std_logic;

        -- WRITE DATA CHANNEL
		m_axi_int_wdata_inmem: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		m_axi_int_wstrb_inmem: out std_logic_vector(C_M_AXI_DATA_WIDTH/8-1 downto 0);
		m_axi_int_wlast_inmem: out std_logic;

		m_axi_int_wvalid_inmem: out std_logic;
		m_axi_int_wready_inmem: in std_logic;

        -- WRITE RESPONSE CHANNEL
		m_axi_int_bresp_inmem: in std_logic_vector(1 downto 0);
		m_axi_int_bvalid_inmem: in std_logic;
		m_axi_int_bready_inmem: out std_logic;

        -- READ ADDRESS CHANNEL
		m_axi_int_araddr_inmem: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		m_axi_int_arlen_inmem: out std_logic_vector(7 downto 0);
		m_axi_int_arsize_inmem: out std_logic_vector(2 downto 0);
		m_axi_int_arburst_inmem: out std_logic_vector(1 downto 0);

		m_axi_int_arvalid_inmem: out std_logic;
		m_axi_int_arready_inmem: in std_logic;

        -- READ DATA CHANNEL
		m_axi_int_rdata_inmem: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		m_axi_int_rresp_inmem: in std_logic_vector(1 downto 0);
		m_axi_int_rlast_inmem: in std_logic;

		m_axi_int_rvalid_inmem: in std_logic;
		m_axi_int_rready_inmem: out std_logic;
		--------------------------------------------------------------------------------

		--------------------------------------------------------------------------------
		-- INTCON PORTS OF OUTGOING MEMORY MODULE S2
		--------------------------------------------------------------------------------

		-- ADDRESS WRITE CHANNEL
		m_axi_int_awaddr_outmem: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		m_axi_int_awlen_outmem: out std_logic_vector(7 downto 0);
		m_axi_int_awsize_outmem: out std_logic_vector(2 downto 0);
		m_axi_int_awburst_outmem: out std_logic_vector(1 downto 0);

		m_axi_int_awvalid_outmem: out std_logic;
		m_axi_int_awready_outmem: in std_logic;

        -- WRITE DATA CHANNEL
		m_axi_int_wdata_outmem: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		m_axi_int_wstrb_outmem: out std_logic_vector(C_M_AXI_DATA_WIDTH/8-1 downto 0);
		m_axi_int_wlast_outmem: out std_logic;

		m_axi_int_wvalid_outmem: out std_logic;
		m_axi_int_wready_outmem: in std_logic;

        -- WRITE RESPONSE CHANNEL
		m_axi_int_bresp_outmem: in std_logic_vector(1 downto 0);
		m_axi_int_bvalid_outmem: in std_logic;
		m_axi_int_bready_outmem: out std_logic;

        -- READ ADDRESS CHANNEL
		m_axi_int_araddr_outmem: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		m_axi_int_arlen_outmem: out std_logic_vector(7 downto 0);
		m_axi_int_arsize_outmem: out std_logic_vector(2 downto 0);
		m_axi_int_arburst_outmem: out std_logic_vector(1 downto 0);

		m_axi_int_arvalid_outmem: out std_logic;
		m_axi_int_arready_outmem: in std_logic;

        -- READ DATA CHANNEL
		m_axi_int_rdata_outmem: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		m_axi_int_rresp_outmem: in std_logic_vector(1 downto 0);
		m_axi_int_rlast_outmem: in std_logic;

		m_axi_int_rvalid_outmem: in std_logic;
		m_axi_int_rready_outmem: out std_logic;
		--------------------------------------------------------------------------------
		--------------------------------------------------------------------------------
		-- INTCON PORTS OF REGISTERS MODULE S3
		--------------------------------------------------------------------------------

        -- ADDRESS WRITE CHANNEL
		m_axi_int_awaddr_reg: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		m_axi_int_awlen_reg: out std_logic_vector(7 downto 0);
		m_axi_int_awsize_reg: out std_logic_vector(2 downto 0);
		m_axi_int_awburst_reg: out std_logic_vector(1 downto 0);

		m_axi_int_awvalid_reg: out std_logic;
		m_axi_int_awready_reg: in std_logic;

        -- WRITE DATA CHANNEL
		m_axi_int_wdata_reg: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		m_axi_int_wstrb_reg: out std_logic_vector(C_M_AXI_DATA_WIDTH/8-1 downto 0);
		m_axi_int_wlast_reg: out std_logic;

		m_axi_int_wvalid_reg: out std_logic;
		m_axi_int_wready_reg: in std_logic;

        -- WRITE RESPONSE CHANNEL
		m_axi_int_bresp_reg: in std_logic_vector(1 downto 0);
		m_axi_int_bvalid_reg: in std_logic;
		m_axi_int_bready_reg: out std_logic;

        -- READ ADDRESS CHANNEL
		m_axi_int_araddr_reg: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		m_axi_int_arlen_reg: out std_logic_vector(7 downto 0);
		m_axi_int_arsize_reg: out std_logic_vector(2 downto 0);
		m_axi_int_arburst_reg: out std_logic_vector(1 downto 0);

		m_axi_int_arvalid_reg: out std_logic;
		m_axi_int_arready_reg: in std_logic;

        -- READ DATA CHANNEL
		m_axi_int_rdata_reg: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		m_axi_int_rresp_reg: in std_logic_vector(1 downto 0);
		m_axi_int_rlast_reg: in std_logic;

		m_axi_int_rvalid_reg: in std_logic;
		m_axi_int_rready_reg: out std_logic;
		--------------------------------------------------------------------------------
		--------------------------------------------------------------------------------
		-- INTCON PORTS OF EXTERNAL REGISTERS MODULE S4
		--------------------------------------------------------------------------------

		-- ADDRESS WRITE CHANNEL
		m_axi_int_awaddr_exreg: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		m_axi_int_awlen_exreg: out std_logic_vector(7 downto 0);
		m_axi_int_awsize_exreg: out std_logic_vector(2 downto 0);
		m_axi_int_awburst_exreg: out std_logic_vector(1 downto 0);

		m_axi_int_awvalid_exreg: out std_logic;
		m_axi_int_awready_exreg: in std_logic;

        -- WRITE DATA CHANNEL
		m_axi_int_wdata_exreg: out std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		m_axi_int_wstrb_exreg: out std_logic_vector(C_M_AXI_DATA_WIDTH/8-1 downto 0);
		m_axi_int_wlast_exreg: out std_logic;

		m_axi_int_wvalid_exreg: out std_logic;
		m_axi_int_wready_exreg: in std_logic;

        -- WRITE RESPONSE CHANNEL
		m_axi_int_bresp_exreg: in std_logic_vector(1 downto 0);
		m_axi_int_bvalid_exreg: in std_logic;
		m_axi_int_bready_exreg: out std_logic;

        -- READ ADDRESS CHANNEL
		m_axi_int_araddr_exreg: out std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
		m_axi_int_arlen_exreg: out std_logic_vector(7 downto 0);
		m_axi_int_arsize_exreg: out std_logic_vector(2 downto 0);
		m_axi_int_arburst_exreg: out std_logic_vector(1 downto 0);

		m_axi_int_arvalid_exreg: out std_logic;
		m_axi_int_arready_exreg: in std_logic;

        -- READ DATA CHANNEL
		m_axi_int_rdata_exreg: in std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
		m_axi_int_rresp_exreg: in std_logic_vector(1 downto 0);
		m_axi_int_rlast_exreg: in std_logic;

		m_axi_int_rvalid_exreg: in std_logic;
		m_axi_int_rready_exreg: out std_logic
		--------------------------------------------------------------------------------

	);
  end component;
  
  --------------------------------------------------------------------------------
  -- MASTERS
  --------------------------------------------------------------------------------

  component controller is
    generic(
        C_M_AXI_BURST_LEN	: integer	:= 16;
        C_M_AXI_ADDR_WIDTH	: integer	:= 32;
        C_M_AXI_DATA_WIDTH	: integer	:= 32
    );
    port (

        -- INTERRUPT PORTS
        ext_irq : in std_logic_vector(1 downto 0);
        int_irq : in std_logic_vector(2 downto 0);

        -- FIXME Delete Users ports 

        AXI_BASE_ADDRESS_I  : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- base address    
        --  WRITE CHANNEL
        AXI_WRITE_ADDRESS_I : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- address added
                                            -- to base address
        AXI_WRITE_INIT_I    : in  std_logic;  -- start write transactions    
        AXI_WRITE_DATA_I    : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
        AXI_WRITE_VLD_I     : in  std_logic;  --  indicates that write data is valid
        AXI_WRITE_RDY_O     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
        AXI_WRITE_DONE_O    : out std_logic;  -- indicates that burst has finished
        -- READ CHANNEL

        AXI_READ_ADDRESS_I : in std_logic_vector(31 downto 0);  -- address added
                                                                -- to base address

        AXI_READ_INIT_I : in  std_logic;    --starts read transaction
        AXI_READ_DATA_O : out std_logic_vector(31 downto 0);  -- data read from                                                             -- ddr
        AXI_READ_VLD_O  : out std_logic;    -- axi_read_data_o is valid
        AXI_READ_RDY_I  : in std_logic;    -- axi_read_data_o is valid
        AXI_READ_LAST_O : out std_logic;    -- axi_read_data_o is valid

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
  end component;

  component packet_builder1 is
    generic(
        C_M_AXI_BURST_LEN	: integer	:= 16;
        C_M_AXI_ADDR_WIDTH	: integer	:= 32;
        C_M_AXI_DATA_WIDTH	: integer	:= 32
    );
    port (

        -- INTERRUPT PORTS
        ext_irq : in std_logic_vector(1 downto 0);
        int_irq : in std_logic_vector(2 downto 0);


        -- FIXME Delete Users ports 

        AXI_BASE_ADDRESS_I  : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- base address    
        --  WRITE CHANNEL
        AXI_WRITE_ADDRESS_I : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- address added
                                            -- to base address
        AXI_WRITE_INIT_I    : in  std_logic;  -- start write transactions    
        AXI_WRITE_DATA_I    : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
        AXI_WRITE_VLD_I     : in  std_logic;  --  indicates that write data is valid
        AXI_WRITE_RDY_O     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
        AXI_WRITE_DONE_O    : out std_logic;  -- indicates that burst has finished
        -- READ CHANNEL

        AXI_READ_ADDRESS_I : in std_logic_vector(31 downto 0);  -- address added
                                                                -- to base address

        AXI_READ_INIT_I : in  std_logic;    --starts read transaction
        AXI_READ_DATA_O : out std_logic_vector(31 downto 0);  -- data read from                                                             -- ddr
        AXI_READ_VLD_O  : out std_logic;    -- axi_read_data_o is valid
        AXI_READ_RDY_I  : in std_logic;    -- axi_read_data_o is valid
        AXI_READ_LAST_O : out std_logic;    -- axi_read_data_o is valid

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
  end component;

  component packet_builder2 is
    generic(
        C_M_AXI_BURST_LEN	: integer	:= 16;
        C_M_AXI_ADDR_WIDTH	: integer	:= 32;
        C_M_AXI_DATA_WIDTH	: integer	:= 32
    );
    port (

        -- INTERRUPT PORTS
        ext_irq : in std_logic_vector(1 downto 0);
        int_irq : in std_logic_vector(2 downto 0);


        -- FIXME Delete Users ports 

        AXI_BASE_ADDRESS_I  : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- base address    
        --  WRITE CHANNEL
        AXI_WRITE_ADDRESS_I : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- address added
                                            -- to base address
        AXI_WRITE_INIT_I    : in  std_logic;  -- start write transactions    
        AXI_WRITE_DATA_I    : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
        AXI_WRITE_VLD_I     : in  std_logic;  --  indicates that write data is valid
        AXI_WRITE_RDY_O     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
        AXI_WRITE_DONE_O    : out std_logic;  -- indicates that burst has finished
        -- READ CHANNEL

        AXI_READ_ADDRESS_I : in std_logic_vector(31 downto 0);  -- address added
                                                                -- to base address

        AXI_READ_INIT_I : in  std_logic;    --starts read transaction
        AXI_READ_DATA_O : out std_logic_vector(31 downto 0);  -- data read from                                                             -- ddr
        AXI_READ_VLD_O  : out std_logic;    -- axi_read_data_o is valid
        AXI_READ_RDY_I  : in std_logic;    -- axi_read_data_o is valid
        AXI_READ_LAST_O : out std_logic;    -- axi_read_data_o is valid

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
  end component;

  component packet_parser is
    generic(
        C_M_AXI_BURST_LEN	: integer	:= 16;
        C_M_AXI_ADDR_WIDTH	: integer	:= 32;
        C_M_AXI_DATA_WIDTH	: integer	:= 32
    );
    port (

        -- INTERRUPT PORTS
        ext_irq : in std_logic_vector(1 downto 0);
        int_irq : in std_logic_vector(2 downto 0);


        -- FIXME Delete Users ports 

        AXI_BASE_ADDRESS_I  : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- base address    
        --  WRITE CHANNEL
        AXI_WRITE_ADDRESS_I : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- address added
                                            -- to base address
        AXI_WRITE_INIT_I    : in  std_logic;  -- start write transactions    
        AXI_WRITE_DATA_I    : in  std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
        AXI_WRITE_VLD_I     : in  std_logic;  --  indicates that write data is valid
        AXI_WRITE_RDY_O     : out std_logic;  -- indicates that controler is ready to                                          -- accept data
        AXI_WRITE_DONE_O    : out std_logic;  -- indicates that burst has finished
        -- READ CHANNEL

        AXI_READ_ADDRESS_I : in std_logic_vector(31 downto 0);  -- address added
                                                                -- to base address

        AXI_READ_INIT_I : in  std_logic;    --starts read transaction
        AXI_READ_DATA_O : out std_logic_vector(31 downto 0);  -- data read from                                                             -- ddr
        AXI_READ_VLD_O  : out std_logic;    -- axi_read_data_o is valid
        AXI_READ_RDY_I  : in std_logic;    -- axi_read_data_o is valid
        AXI_READ_LAST_O : out std_logic;    -- axi_read_data_o is valid

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
  end component;
  --------------------------------------------------------------------------------
  -- SLAVES
  --------------------------------------------------------------------------------
  component incomming_data_memory is
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
  end component;

  component outgoing_data_memory is
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
  end component;

  component regs is
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
		-- SLAVE INTERFACE WRITE ADDRESS
		--------------------------------------------------------------------------------
		-- Write address
		S_AXI_AWADDR	: in std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		-- Burst length. The burst length gives the exact number of transfers in a burst
		-- S_AXI_AWLEN	: in std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		-- S_AXI_AWSIZE	: in std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		-- S_AXI_AWBURST	: in std_logic_vector(1 downto 0);
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
		-- S_AXI_WLAST	: in std_logic;
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
		-- S_AXI_ARLEN	: in std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		-- S_AXI_ARSIZE	: in std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		-- S_AXI_ARBURST	: in std_logic_vector(1 downto 0);
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
		-- S_AXI_RLAST	: out std_logic;
		-- Read valid. This signal indicates that the channel
    -- is signaling the required read data.
		S_AXI_RVALID	: out std_logic;
		-- Read ready. This signal indicates that the master can
    -- accept the read data and response information.
		S_AXI_RREADY	: in std_logic
  );
  end component;

  component external_regs is
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
		-- SLAVE INTERFACE WRITE ADDRESS
		--------------------------------------------------------------------------------
		-- Write address
		S_AXI_AWADDR	: in std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
		-- Burst length. The burst length gives the exact number of transfers in a burst
		-- S_AXI_AWLEN	: in std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		-- S_AXI_AWSIZE	: in std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		-- S_AXI_AWBURST	: in std_logic_vector(1 downto 0);
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
		-- S_AXI_WLAST	: in std_logic;
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
		-- S_AXI_ARLEN	: in std_logic_vector(7 downto 0);
		-- Burst size. This signal indicates the size of each transfer in the burst
		-- S_AXI_ARSIZE	: in std_logic_vector(2 downto 0);
		-- Burst type. The burst type and the size information, 
    -- determine how the address for each transfer within the burst is calculated.
		-- S_AXI_ARBURST	: in std_logic_vector(1 downto 0);
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
		-- S_AXI_RLAST	: out std_logic;
		-- Read valid. This signal indicates that the channel
    -- is signaling the required read data.
		S_AXI_RVALID	: out std_logic;
		-- Read ready. This signal indicates that the master can
    -- accept the read data and response information.
		S_AXI_RREADY	: in std_logic
  );
  end component;


  --------------------------------------------------------------------------------
  -- MASTERS signals connections
  --------------------------------------------------------------------------------
  signal s_axi_int_awaddr_ctrl : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal s_axi_int_awlen_ctrl : std_logic_vector(7 downto 0);
  signal s_axi_int_awsize_ctrl : std_logic_vector(2 downto 0);
  signal s_axi_int_awburst_ctrl : std_logic_vector(1 downto 0);
  signal s_axi_int_awvalid_ctrl : std_logic;
  signal s_axi_int_awready_ctrl : std_logic;
  signal s_axi_int_wdata_ctrl : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_axi_int_wstrb_ctrl : std_logic_vector((DATA_WIDTH/8)-1 downto 0);
  signal s_axi_int_wlast_ctrl : std_logic;
  signal s_axi_int_wvalid_ctrl : std_logic;
  signal s_axi_int_wready_ctrl : std_logic;
  signal s_axi_int_bresp_ctrl : std_logic_vector(1 downto 0);
  signal s_axi_int_bvalid_ctrl : std_logic;
  signal s_axi_int_bready_ctrl : std_logic;
  signal s_axi_int_araddr_ctrl : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal s_axi_int_arlen_ctrl : std_logic_vector(7 downto 0);
  signal s_axi_int_arsize_ctrl : std_logic_vector(2 downto 0);
  signal s_axi_int_arburst_ctrl : std_logic_vector(1 downto 0);
  signal s_axi_int_arvalid_ctrl : std_logic;
  signal s_axi_int_arready_ctrl : std_logic;
  signal s_axi_int_rdata_ctrl : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_axi_int_rresp_ctrl : std_logic_vector(1 downto 0);
  signal s_axi_int_rlast_ctrl : std_logic;
  signal s_axi_int_rvalid_ctrl : std_logic;
  signal s_axi_int_rready_ctrl : std_logic;
  --------------------------------------------------------------------------------

  signal s_axi_int_awaddr_pb0 : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal s_axi_int_awlen_pb0 : std_logic_vector(7 downto 0);
  signal s_axi_int_awsize_pb0 : std_logic_vector(2 downto 0);
  signal s_axi_int_awburst_pb0 : std_logic_vector(1 downto 0);
  signal s_axi_int_awvalid_pb0 : std_logic;
  signal s_axi_int_awready_pb0 : std_logic;
  signal s_axi_int_wdata_pb0 : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_axi_int_wstrb_pb0 : std_logic_vector((DATA_WIDTH/8)-1 downto 0);
  signal s_axi_int_wlast_pb0 : std_logic;
  signal s_axi_int_wvalid_pb0 : std_logic;
  signal s_axi_int_wready_pb0 : std_logic;
  signal s_axi_int_bresp_pb0 : std_logic_vector(1 downto 0);
  signal s_axi_int_bvalid_pb0 : std_logic;
  signal s_axi_int_bready_pb0 : std_logic;
  signal s_axi_int_araddr_pb0 : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal s_axi_int_arlen_pb0 : std_logic_vector(7 downto 0);
  signal s_axi_int_arsize_pb0 : std_logic_vector(2 downto 0);
  signal s_axi_int_arburst_pb0 : std_logic_vector(1 downto 0);
  signal s_axi_int_arvalid_pb0 : std_logic;
  signal s_axi_int_arready_pb0 : std_logic;
  signal s_axi_int_rdata_pb0 : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_axi_int_rresp_pb0 : std_logic_vector(1 downto 0);
  signal s_axi_int_rlast_pb0 : std_logic;
  signal s_axi_int_rvalid_pb0 : std_logic;
  signal s_axi_int_rready_pb0 : std_logic;
  --------------------------------------------------------------------------------
  
  signal s_axi_int_awaddr_pb1 : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal s_axi_int_awlen_pb1 : std_logic_vector(7 downto 0);
  signal s_axi_int_awsize_pb1 : std_logic_vector(2 downto 0);
  signal s_axi_int_awburst_pb1 : std_logic_vector(1 downto 0);
  signal s_axi_int_awvalid_pb1 : std_logic;
  signal s_axi_int_awready_pb1 : std_logic;
  signal s_axi_int_wdata_pb1 : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_axi_int_wstrb_pb1 : std_logic_vector((DATA_WIDTH/8)-1 downto 0);
  signal s_axi_int_wlast_pb1 : std_logic;
  signal s_axi_int_wvalid_pb1 : std_logic;
  signal s_axi_int_wready_pb1 : std_logic;
  signal s_axi_int_bresp_pb1 : std_logic_vector(1 downto 0);
  signal s_axi_int_bvalid_pb1 : std_logic;
  signal s_axi_int_bready_pb1 : std_logic;
  signal s_axi_int_araddr_pb1 : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal s_axi_int_arlen_pb1 : std_logic_vector(7 downto 0);
  signal s_axi_int_arsize_pb1 : std_logic_vector(2 downto 0);
  signal s_axi_int_arburst_pb1 : std_logic_vector(1 downto 0);
  signal s_axi_int_arvalid_pb1 : std_logic;
  signal s_axi_int_arready_pb1 : std_logic;
  signal s_axi_int_rdata_pb1 : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_axi_int_rresp_pb1 : std_logic_vector(1 downto 0);
  signal s_axi_int_rlast_pb1 : std_logic;
  signal s_axi_int_rvalid_pb1 : std_logic;
  signal s_axi_int_rready_pb1 : std_logic;
  --------------------------------------------------------------------------------

  signal s_axi_int_awaddr_pp : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal s_axi_int_awlen_pp : std_logic_vector(7 downto 0);
  signal s_axi_int_awsize_pp : std_logic_vector(2 downto 0);
  signal s_axi_int_awburst_pp : std_logic_vector(1 downto 0);
  signal s_axi_int_awvalid_pp : std_logic;
  signal s_axi_int_awready_pp : std_logic;
  signal s_axi_int_wdata_pp : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_axi_int_wstrb_pp : std_logic_vector((DATA_WIDTH/8)-1 downto 0);
  signal s_axi_int_wlast_pp : std_logic;
  signal s_axi_int_wvalid_pp : std_logic;
  signal s_axi_int_wready_pp : std_logic;
  signal s_axi_int_bresp_pp : std_logic_vector(1 downto 0);
  signal s_axi_int_bvalid_pp : std_logic;
  signal s_axi_int_bready_pp : std_logic;
  signal s_axi_int_araddr_pp : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal s_axi_int_arlen_pp : std_logic_vector(7 downto 0);
  signal s_axi_int_arsize_pp : std_logic_vector(2 downto 0);
  signal s_axi_int_arburst_pp : std_logic_vector(1 downto 0);
  signal s_axi_int_arvalid_pp : std_logic;
  signal s_axi_int_arready_pp : std_logic;
  signal s_axi_int_rdata_pp : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_axi_int_rresp_pp : std_logic_vector(1 downto 0);
  signal s_axi_int_rlast_pp : std_logic;
  signal s_axi_int_rvalid_pp : std_logic;
  signal s_axi_int_rready_pp : std_logic;
  --------------------------------------------------------------------------------

  --------------------------------------------------------------------------------
  -- SLAVES
  --------------------------------------------------------------------------------
  signal m_axi_int_awaddr_inmem : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal m_axi_int_awlen_inmem : std_logic_vector(7 downto 0);
  signal m_axi_int_awsize_inmem : std_logic_vector(2 downto 0);
  signal m_axi_int_awburst_inmem : std_logic_vector(1 downto 0);
  signal m_axi_int_awvalid_inmem : std_logic;
  signal m_axi_int_awready_inmem : std_logic;
  signal m_axi_int_wdata_inmem : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal m_axi_int_wstrb_inmem : std_logic_vector(DATA_WIDTH/8-1 downto 0);
  signal m_axi_int_wlast_inmem : std_logic;
  signal m_axi_int_wvalid_inmem : std_logic;
  signal m_axi_int_wready_inmem : std_logic;
  signal m_axi_int_bresp_inmem : std_logic_vector(1 downto 0);
  signal m_axi_int_bvalid_inmem : std_logic;
  signal m_axi_int_bready_inmem : std_logic;
  signal m_axi_int_araddr_inmem : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal m_axi_int_arlen_inmem : std_logic_vector(7 downto 0);
  signal m_axi_int_arsize_inmem : std_logic_vector(2 downto 0);
  signal m_axi_int_arburst_inmem : std_logic_vector(1 downto 0);
  signal m_axi_int_arvalid_inmem : std_logic;
  signal m_axi_int_arready_inmem : std_logic;
  signal m_axi_int_rdata_inmem : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal m_axi_int_rresp_inmem : std_logic_vector(1 downto 0);
  signal m_axi_int_rlast_inmem : std_logic;
  signal m_axi_int_rvalid_inmem : std_logic;
  signal m_axi_int_rready_inmem : std_logic;
  --------------------------------------------------------------------------------

  signal m_axi_int_awaddr_outmem : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal m_axi_int_awlen_outmem : std_logic_vector(7 downto 0);
  signal m_axi_int_awsize_outmem : std_logic_vector(2 downto 0);
  signal m_axi_int_awburst_outmem : std_logic_vector(1 downto 0);
  signal m_axi_int_awvalid_outmem : std_logic;
  signal m_axi_int_awready_outmem : std_logic;
  signal m_axi_int_wdata_outmem : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal m_axi_int_wstrb_outmem : std_logic_vector(DATA_WIDTH/8-1 downto 0);
  signal m_axi_int_wlast_outmem : std_logic;
  signal m_axi_int_wvalid_outmem : std_logic;
  signal m_axi_int_wready_outmem : std_logic;
  signal m_axi_int_bresp_outmem : std_logic_vector(1 downto 0);
  signal m_axi_int_bvalid_outmem : std_logic;
  signal m_axi_int_bready_outmem : std_logic;
  signal m_axi_int_araddr_outmem : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal m_axi_int_arlen_outmem : std_logic_vector(7 downto 0);
  signal m_axi_int_arsize_outmem : std_logic_vector(2 downto 0);
  signal m_axi_int_arburst_outmem : std_logic_vector(1 downto 0);
  signal m_axi_int_arvalid_outmem : std_logic;
  signal m_axi_int_arready_outmem : std_logic;
  signal m_axi_int_rdata_outmem : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal m_axi_int_rresp_outmem : std_logic_vector(1 downto 0);
  signal m_axi_int_rlast_outmem : std_logic;
  signal m_axi_int_rvalid_outmem : std_logic;
  signal m_axi_int_rready_outmem : std_logic;
  --------------------------------------------------------------------------------

  signal m_axi_int_awaddr_reg : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal m_axi_int_awlen_reg : std_logic_vector(7 downto 0);
  signal m_axi_int_awsize_reg : std_logic_vector(2 downto 0);
  signal m_axi_int_awburst_reg : std_logic_vector(1 downto 0);
  signal m_axi_int_awvalid_reg : std_logic;
  signal m_axi_int_awready_reg : std_logic;
  signal m_axi_int_wdata_reg : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal m_axi_int_wstrb_reg : std_logic_vector(DATA_WIDTH/8-1 downto 0);
  signal m_axi_int_wlast_reg : std_logic;
  signal m_axi_int_wvalid_reg : std_logic;
  signal m_axi_int_wready_reg : std_logic;
  signal m_axi_int_bresp_reg : std_logic_vector(1 downto 0);
  signal m_axi_int_bvalid_reg : std_logic;
  signal m_axi_int_bready_reg : std_logic;
  signal m_axi_int_araddr_reg : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal m_axi_int_arlen_reg : std_logic_vector(7 downto 0);
  signal m_axi_int_arsize_reg : std_logic_vector(2 downto 0);
  signal m_axi_int_arburst_reg : std_logic_vector(1 downto 0);
  signal m_axi_int_arvalid_reg : std_logic;
  signal m_axi_int_arready_reg : std_logic;
  signal m_axi_int_rdata_reg : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal m_axi_int_rresp_reg : std_logic_vector(1 downto 0);
  signal m_axi_int_rlast_reg : std_logic;
  signal m_axi_int_rvalid_reg : std_logic;
  signal m_axi_int_rready_reg : std_logic;
  --------------------------------------------------------------------------------

  signal m_axi_int_awaddr_exreg : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal m_axi_int_awlen_exreg : std_logic_vector(7 downto 0);
  signal m_axi_int_awsize_exreg : std_logic_vector(2 downto 0);
  signal m_axi_int_awburst_exreg : std_logic_vector(1 downto 0);
  signal m_axi_int_awvalid_exreg : std_logic;
  signal m_axi_int_awready_exreg : std_logic;
  signal m_axi_int_wdata_exreg : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal m_axi_int_wstrb_exreg : std_logic_vector(DATA_WIDTH/8-1 downto 0);
  signal m_axi_int_wlast_exreg : std_logic;
  signal m_axi_int_wvalid_exreg : std_logic;
  signal m_axi_int_wready_exreg : std_logic;
  signal m_axi_int_bresp_exreg : std_logic_vector(1 downto 0);
  signal m_axi_int_bvalid_exreg : std_logic;
  signal m_axi_int_bready_exreg : std_logic;
  signal m_axi_int_araddr_exreg : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal m_axi_int_arlen_exreg : std_logic_vector(7 downto 0);
  signal m_axi_int_arsize_exreg : std_logic_vector(2 downto 0);
  signal m_axi_int_arburst_exreg : std_logic_vector(1 downto 0);
  signal m_axi_int_arvalid_exreg : std_logic;
  signal m_axi_int_arready_exreg : std_logic;
  signal m_axi_int_rdata_exreg : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal m_axi_int_rresp_exreg : std_logic_vector(1 downto 0);
  signal m_axi_int_rlast_exreg : std_logic;
  signal m_axi_int_rvalid_exreg : std_logic;
  signal m_axi_int_rready_exreg : std_logic;
  --------------------------------------------------------------------------------

begin

  intcon: interconnect
  generic map(
    C_M_AXI_ADDR_WIDTH => ADDR_WIDTH,
    C_M_AXI_DATA_WIDTH => DATA_WIDTH

  )
  port map(
		clk	=> clk,
		reset	=> reset,
    --------------------------------------------------------------------------------
    -- MASTERS signals connections
    --------------------------------------------------------------------------------
    s_axi_int_awaddr_ctrl => s_axi_int_awaddr_ctrl,
    s_axi_int_awlen_ctrl => s_axi_int_awlen_ctrl,
    s_axi_int_awsize_ctrl => s_axi_int_awsize_ctrl,
    s_axi_int_awburst_ctrl => s_axi_int_awburst_ctrl,
    s_axi_int_awvalid_ctrl => s_axi_int_awvalid_ctrl,
    s_axi_int_awready_ctrl => s_axi_int_awready_ctrl,
    s_axi_int_wdata_ctrl => s_axi_int_wdata_ctrl,
    s_axi_int_wstrb_ctrl => s_axi_int_wstrb_ctrl,
    s_axi_int_wlast_ctrl => s_axi_int_wlast_ctrl,
    s_axi_int_wvalid_ctrl => s_axi_int_wvalid_ctrl,
    s_axi_int_wready_ctrl => s_axi_int_wready_ctrl,
    s_axi_int_bresp_ctrl => s_axi_int_bresp_ctrl,
    s_axi_int_bvalid_ctrl => s_axi_int_bvalid_ctrl,
    s_axi_int_bready_ctrl => s_axi_int_bready_ctrl,
    s_axi_int_araddr_ctrl => s_axi_int_araddr_ctrl,
    s_axi_int_arlen_ctrl => s_axi_int_arlen_ctrl,
    s_axi_int_arsize_ctrl => s_axi_int_arsize_ctrl,
    s_axi_int_arburst_ctrl => s_axi_int_arburst_ctrl,
    s_axi_int_arvalid_ctrl => s_axi_int_arvalid_ctrl,
    s_axi_int_arready_ctrl => s_axi_int_arready_ctrl,
    s_axi_int_rdata_ctrl => s_axi_int_rdata_ctrl,
    s_axi_int_rresp_ctrl => s_axi_int_rresp_ctrl,
    s_axi_int_rlast_ctrl => s_axi_int_rlast_ctrl,
    s_axi_int_rvalid_ctrl => s_axi_int_rvalid_ctrl,
    s_axi_int_rready_ctrl => s_axi_int_rready_ctrl,
    --------------------------------------------------------------------------------

    s_axi_int_awaddr_pb0 => s_axi_int_awaddr_pb0,
    s_axi_int_awlen_pb0 => s_axi_int_awlen_pb0,
    s_axi_int_awsize_pb0 => s_axi_int_awsize_pb0,
    s_axi_int_awburst_pb0 => s_axi_int_awburst_pb0,
    s_axi_int_awvalid_pb0 => s_axi_int_awvalid_pb0,
    s_axi_int_awready_pb0 => s_axi_int_awready_pb0,
    s_axi_int_wdata_pb0 => s_axi_int_wdata_pb0,
    s_axi_int_wstrb_pb0 => s_axi_int_wstrb_pb0,
    s_axi_int_wlast_pb0 => s_axi_int_wlast_pb0,
    s_axi_int_wvalid_pb0 => s_axi_int_wvalid_pb0,
    s_axi_int_wready_pb0 => s_axi_int_wready_pb0,
    s_axi_int_bresp_pb0 => s_axi_int_bresp_pb0,
    s_axi_int_bvalid_pb0 => s_axi_int_bvalid_pb0,
    s_axi_int_bready_pb0 => s_axi_int_bready_pb0,
    s_axi_int_araddr_pb0 => s_axi_int_araddr_pb0,
    s_axi_int_arlen_pb0 => s_axi_int_arlen_pb0,
    s_axi_int_arsize_pb0 => s_axi_int_arsize_pb0,
    s_axi_int_arburst_pb0 => s_axi_int_arburst_pb0,
    s_axi_int_arvalid_pb0 => s_axi_int_arvalid_pb0,
    s_axi_int_arready_pb0 => s_axi_int_arready_pb0,
    s_axi_int_rdata_pb0 => s_axi_int_rdata_pb0,
    s_axi_int_rresp_pb0 => s_axi_int_rresp_pb0,
    s_axi_int_rlast_pb0 => s_axi_int_rlast_pb0,
    s_axi_int_rvalid_pb0 => s_axi_int_rvalid_pb0,
    s_axi_int_rready_pb0 => s_axi_int_rready_pb0,
    --------------------------------------------------------------------------------
    
    s_axi_int_awaddr_pb1 => s_axi_int_awaddr_pb1,
    s_axi_int_awlen_pb1 => s_axi_int_awlen_pb1,
    s_axi_int_awsize_pb1 => s_axi_int_awsize_pb1,
    s_axi_int_awburst_pb1 => s_axi_int_awburst_pb1,
    s_axi_int_awvalid_pb1 => s_axi_int_awvalid_pb1,
    s_axi_int_awready_pb1 => s_axi_int_awready_pb1,
    s_axi_int_wdata_pb1 => s_axi_int_wdata_pb1,
    s_axi_int_wstrb_pb1 => s_axi_int_wstrb_pb1,
    s_axi_int_wlast_pb1 => s_axi_int_wlast_pb1,
    s_axi_int_wvalid_pb1 => s_axi_int_wvalid_pb1,
    s_axi_int_wready_pb1 => s_axi_int_wready_pb1,
    s_axi_int_bresp_pb1 => s_axi_int_bresp_pb1,
    s_axi_int_bvalid_pb1 => s_axi_int_bvalid_pb1,
    s_axi_int_bready_pb1 => s_axi_int_bready_pb1,
    s_axi_int_araddr_pb1 => s_axi_int_araddr_pb1,
    s_axi_int_arlen_pb1 => s_axi_int_arlen_pb1,
    s_axi_int_arsize_pb1 => s_axi_int_arsize_pb1,
    s_axi_int_arburst_pb1 => s_axi_int_arburst_pb1,
    s_axi_int_arvalid_pb1 => s_axi_int_arvalid_pb1,
    s_axi_int_arready_pb1 => s_axi_int_arready_pb1,
    s_axi_int_rdata_pb1 => s_axi_int_rdata_pb1,
    s_axi_int_rresp_pb1 => s_axi_int_rresp_pb1,
    s_axi_int_rlast_pb1 => s_axi_int_rlast_pb1,
    s_axi_int_rvalid_pb1 => s_axi_int_rvalid_pb1,
    s_axi_int_rready_pb1 => s_axi_int_rready_pb1,
    --------------------------------------------------------------------------------

    s_axi_int_awaddr_pp => s_axi_int_awaddr_pp,
    s_axi_int_awlen_pp => s_axi_int_awlen_pp,
    s_axi_int_awsize_pp => s_axi_int_awsize_pp,
    s_axi_int_awburst_pp => s_axi_int_awburst_pp,
    s_axi_int_awvalid_pp => s_axi_int_awvalid_pp,
    s_axi_int_awready_pp => s_axi_int_awready_pp,
    s_axi_int_wdata_pp => s_axi_int_wdata_pp,
    s_axi_int_wstrb_pp => s_axi_int_wstrb_pp,
    s_axi_int_wlast_pp => s_axi_int_wlast_pp,
    s_axi_int_wvalid_pp => s_axi_int_wvalid_pp,
    s_axi_int_wready_pp => s_axi_int_wready_pp,
    s_axi_int_bresp_pp => s_axi_int_bresp_pp,
    s_axi_int_bvalid_pp => s_axi_int_bvalid_pp,
    s_axi_int_bready_pp => s_axi_int_bready_pp,
    s_axi_int_araddr_pp => s_axi_int_araddr_pp,
    s_axi_int_arlen_pp => s_axi_int_arlen_pp,
    s_axi_int_arsize_pp => s_axi_int_arsize_pp,
    s_axi_int_arburst_pp => s_axi_int_arburst_pp,
    s_axi_int_arvalid_pp => s_axi_int_arvalid_pp,
    s_axi_int_arready_pp => s_axi_int_arready_pp,
    s_axi_int_rdata_pp => s_axi_int_rdata_pp,
    s_axi_int_rresp_pp => s_axi_int_rresp_pp,
    s_axi_int_rlast_pp => s_axi_int_rlast_pp,
    s_axi_int_rvalid_pp => s_axi_int_rvalid_pp,
    s_axi_int_rready_pp => s_axi_int_rready_pp,
    --------------------------------------------------------------------------------

    --------------------------------------------------------------------------------
    -- SLAVES
    --------------------------------------------------------------------------------
    m_axi_int_awaddr_inmem => m_axi_int_awaddr_inmem,
    m_axi_int_awlen_inmem => m_axi_int_awlen_inmem,
    m_axi_int_awsize_inmem => m_axi_int_awsize_inmem,
    m_axi_int_awburst_inmem => m_axi_int_awburst_inmem,
    m_axi_int_awvalid_inmem => m_axi_int_awvalid_inmem,
    m_axi_int_awready_inmem => m_axi_int_awready_inmem,
    m_axi_int_wdata_inmem => m_axi_int_wdata_inmem,
    m_axi_int_wstrb_inmem => m_axi_int_wstrb_inmem,
    m_axi_int_wlast_inmem => m_axi_int_wlast_inmem,
    m_axi_int_wvalid_inmem => m_axi_int_wvalid_inmem,
    m_axi_int_wready_inmem => m_axi_int_wready_inmem,
    m_axi_int_bresp_inmem => m_axi_int_bresp_inmem,
    m_axi_int_bvalid_inmem => m_axi_int_bvalid_inmem,
    m_axi_int_bready_inmem => m_axi_int_bready_inmem,
    m_axi_int_araddr_inmem => m_axi_int_araddr_inmem,
    m_axi_int_arlen_inmem => m_axi_int_arlen_inmem,
    m_axi_int_arsize_inmem => m_axi_int_arsize_inmem,
    m_axi_int_arburst_inmem => m_axi_int_arburst_inmem,
    m_axi_int_arvalid_inmem => m_axi_int_arvalid_inmem,
    m_axi_int_arready_inmem => m_axi_int_arready_inmem,
    m_axi_int_rdata_inmem => m_axi_int_rdata_inmem,
    m_axi_int_rresp_inmem => m_axi_int_rresp_inmem,
    m_axi_int_rlast_inmem => m_axi_int_rlast_inmem,
    m_axi_int_rvalid_inmem => m_axi_int_rvalid_inmem,
    m_axi_int_rready_inmem => m_axi_int_rready_inmem,
    --------------------------------------------------------------------------------

    m_axi_int_awaddr_outmem => m_axi_int_awaddr_outmem,
    m_axi_int_awlen_outmem => m_axi_int_awlen_outmem,
    m_axi_int_awsize_outmem => m_axi_int_awsize_outmem,
    m_axi_int_awburst_outmem => m_axi_int_awburst_outmem,
    m_axi_int_awvalid_outmem => m_axi_int_awvalid_outmem,
    m_axi_int_awready_outmem => m_axi_int_awready_outmem,
    m_axi_int_wdata_outmem => m_axi_int_wdata_outmem,
    m_axi_int_wstrb_outmem => m_axi_int_wstrb_outmem,
    m_axi_int_wlast_outmem => m_axi_int_wlast_outmem,
    m_axi_int_wvalid_outmem => m_axi_int_wvalid_outmem,
    m_axi_int_wready_outmem => m_axi_int_wready_outmem,
    m_axi_int_bresp_outmem => m_axi_int_bresp_outmem,
    m_axi_int_bvalid_outmem => m_axi_int_bvalid_outmem,
    m_axi_int_bready_outmem => m_axi_int_bready_outmem,
    m_axi_int_araddr_outmem => m_axi_int_araddr_outmem,
    m_axi_int_arlen_outmem => m_axi_int_arlen_outmem,
    m_axi_int_arsize_outmem => m_axi_int_arsize_outmem,
    m_axi_int_arburst_outmem => m_axi_int_arburst_outmem,
    m_axi_int_arvalid_outmem => m_axi_int_arvalid_outmem,
    m_axi_int_arready_outmem => m_axi_int_arready_outmem,
    m_axi_int_rdata_outmem => m_axi_int_rdata_outmem,
    m_axi_int_rresp_outmem => m_axi_int_rresp_outmem,
    m_axi_int_rlast_outmem => m_axi_int_rlast_outmem,
    m_axi_int_rvalid_outmem => m_axi_int_rvalid_outmem,
    m_axi_int_rready_outmem => m_axi_int_rready_outmem,
    --------------------------------------------------------------------------------

    m_axi_int_awaddr_reg => m_axi_int_awaddr_reg,
    m_axi_int_awlen_reg => open,
    m_axi_int_awsize_reg => open,
    m_axi_int_awburst_reg => open,
    m_axi_int_awvalid_reg => m_axi_int_awvalid_reg,
    m_axi_int_awready_reg => m_axi_int_awready_reg,
    m_axi_int_wdata_reg => m_axi_int_wdata_reg,
    m_axi_int_wstrb_reg => m_axi_int_wstrb_reg,
    m_axi_int_wlast_reg => open,
    m_axi_int_wvalid_reg => m_axi_int_wvalid_reg,
    m_axi_int_wready_reg => m_axi_int_wready_reg,
    m_axi_int_bresp_reg => m_axi_int_bresp_reg,
    m_axi_int_bvalid_reg => m_axi_int_bvalid_reg,
    m_axi_int_bready_reg => m_axi_int_bready_reg,
    m_axi_int_araddr_reg => m_axi_int_araddr_reg,
    m_axi_int_arlen_reg => open,
    m_axi_int_arsize_reg => open,
    m_axi_int_arburst_reg => open,
    m_axi_int_arvalid_reg => m_axi_int_arvalid_reg,
    m_axi_int_arready_reg => m_axi_int_arready_reg,
    m_axi_int_rdata_reg => m_axi_int_rdata_reg,
    m_axi_int_rresp_reg => m_axi_int_rresp_reg,
    m_axi_int_rlast_reg => '1',
    m_axi_int_rvalid_reg => m_axi_int_rvalid_reg,
    m_axi_int_rready_reg => m_axi_int_rready_reg,
    --------------------------------------------------------------------------------

    m_axi_int_awaddr_exreg => m_axi_int_awaddr_exreg,
    m_axi_int_awlen_exreg => open,
    m_axi_int_awsize_exreg => open,
    m_axi_int_awburst_exreg => open,
    m_axi_int_awvalid_exreg => m_axi_int_awvalid_exreg,
    m_axi_int_awready_exreg => m_axi_int_awready_exreg,
    m_axi_int_wdata_exreg => m_axi_int_wdata_exreg,
    m_axi_int_wstrb_exreg => m_axi_int_wstrb_exreg,
    m_axi_int_wlast_exreg => open,
    m_axi_int_wvalid_exreg => m_axi_int_wvalid_exreg,
    m_axi_int_wready_exreg => m_axi_int_wready_exreg,
    m_axi_int_bresp_exreg => m_axi_int_bresp_exreg,
    m_axi_int_bvalid_exreg => m_axi_int_bvalid_exreg,
    m_axi_int_bready_exreg => m_axi_int_bready_exreg,
    m_axi_int_araddr_exreg => m_axi_int_araddr_exreg,
    m_axi_int_arlen_exreg => open,
    m_axi_int_arsize_exreg => open,
    m_axi_int_arburst_exreg => open,
    m_axi_int_arvalid_exreg => m_axi_int_arvalid_exreg,
    m_axi_int_arready_exreg => m_axi_int_arready_exreg,
    m_axi_int_rdata_exreg => m_axi_int_rdata_exreg,
    m_axi_int_rresp_exreg => m_axi_int_rresp_exreg,
    m_axi_int_rlast_exreg => '1',
    m_axi_int_rvalid_exreg => m_axi_int_rvalid_exreg,
    m_axi_int_rready_exreg => m_axi_int_rready_exreg
    --------------------------------------------------------------------------------


  );

  main_controller: controller
  generic map (

    C_M_AXI_DATA_WIDTH => DATA_WIDTH,
    C_M_AXI_ADDR_WIDTH => ADDR_WIDTH,
    C_M_AXI_BURST_LEN => BURST_LEN
  ) 
  port map(
        ext_irq => (others => '0'),
        int_irq => (others => '0'),

        -- FIXME Delete Users ports 

        AXI_BASE_ADDRESS_I => AXI_BASE_ADDRESS_I_CTRL,  
        AXI_WRITE_ADDRESS_I => AXI_WRITE_ADDRESS_I_CTRL,
        AXI_WRITE_INIT_I => AXI_WRITE_INIT_I_CTRL,    
        AXI_WRITE_DATA_I => AXI_WRITE_DATA_I_CTRL,
        AXI_WRITE_VLD_I => AXI_WRITE_VLD_I_CTRL,
        AXI_WRITE_RDY_O => AXI_WRITE_RDY_O_CTRL,
        AXI_WRITE_DONE_O => AXI_WRITE_DONE_O_CTRL,
        AXI_READ_ADDRESS_I => AXI_READ_ADDRESS_I_CTRL,
        AXI_READ_INIT_I => AXI_READ_INIT_I_CTRL,
        AXI_READ_DATA_O => AXI_READ_DATA_O_CTRL,
        AXI_READ_VLD_O => AXI_READ_VLD_O_CTRL,
        AXI_READ_RDY_I => AXI_READ_RDY_I_CTRL,
        AXI_READ_LAST_O => AXI_READ_LAST_O_CTRL,

        M_AXI_ACLK => clk,
        M_AXI_ARESETN => reset,

        M_AXI_AWADDR => s_axi_int_awaddr_ctrl,
        M_AXI_AWLEN => s_axi_int_awlen_ctrl,
        M_AXI_AWSIZE => s_axi_int_awsize_ctrl,
        M_AXI_AWBURST => s_axi_int_awburst_ctrl,
        M_AXI_AWVALID => s_axi_int_awvalid_ctrl,
        M_AXI_AWREADY => s_axi_int_awready_ctrl,
        M_AXI_WDATA => s_axi_int_wdata_ctrl,
        M_AXI_WSTRB => s_axi_int_wstrb_ctrl,
        M_AXI_WLAST => s_axi_int_wlast_ctrl,
        M_AXI_WVALID => s_axi_int_wvalid_ctrl,
        M_AXI_WREADY => s_axi_int_wready_ctrl,
        M_AXI_BRESP => s_axi_int_bresp_ctrl,
        M_AXI_BVALID => s_axi_int_bvalid_ctrl,
        M_AXI_BREADY => s_axi_int_bready_ctrl,
        M_AXI_ARADDR => s_axi_int_araddr_ctrl,
        M_AXI_ARLEN => s_axi_int_arlen_ctrl,
        M_AXI_ARSIZE => s_axi_int_arsize_ctrl,
        M_AXI_ARBURST => s_axi_int_arburst_ctrl,
        M_AXI_ARVALID => s_axi_int_arvalid_ctrl,
        M_AXI_ARREADY => s_axi_int_arready_ctrl,
        M_AXI_RDATA => s_axi_int_rdata_ctrl,
        M_AXI_RRESP => s_axi_int_rresp_ctrl,
        M_AXI_RLAST => s_axi_int_rlast_ctrl,
        M_AXI_RVALID => s_axi_int_rvalid_ctrl,
        M_AXI_RREADY => s_axi_int_rready_ctrl

  );

  builder1: packet_builder1
  generic map (

    C_M_AXI_DATA_WIDTH => DATA_WIDTH,
    C_M_AXI_ADDR_WIDTH => ADDR_WIDTH,
    C_M_AXI_BURST_LEN => BURST_LEN
  ) 
  port map(
        ext_irq => (others => '0'),
        int_irq => (others => '0'),

        -- FIXME Delete Users ports 

        AXI_BASE_ADDRESS_I => AXI_BASE_ADDRESS_I_PB0,  
        AXI_WRITE_ADDRESS_I => AXI_WRITE_ADDRESS_I_PB0,
        AXI_WRITE_INIT_I => AXI_WRITE_INIT_I_PB0,    
        AXI_WRITE_DATA_I => AXI_WRITE_DATA_I_PB0,
        AXI_WRITE_VLD_I => AXI_WRITE_VLD_I_PB0,
        AXI_WRITE_RDY_O => AXI_WRITE_RDY_O_PB0,
        AXI_WRITE_DONE_O => AXI_WRITE_DONE_O_PB0,
        AXI_READ_ADDRESS_I => AXI_READ_ADDRESS_I_PB0,
        AXI_READ_INIT_I => AXI_READ_INIT_I_PB0,
        AXI_READ_DATA_O => AXI_READ_DATA_O_PB0,
        AXI_READ_VLD_O => AXI_READ_VLD_O_PB0,
        AXI_READ_RDY_I => AXI_READ_RDY_I_PB0,
        AXI_READ_LAST_O => AXI_READ_LAST_O_PB0,

        M_AXI_ACLK => clk,
        M_AXI_ARESETN => reset,

        M_AXI_AWADDR => s_axi_int_awaddr_pb0,
        M_AXI_AWLEN => s_axi_int_awlen_pb0,
        M_AXI_AWSIZE => s_axi_int_awsize_pb0,
        M_AXI_AWBURST => s_axi_int_awburst_pb0,
        M_AXI_AWVALID => s_axi_int_awvalid_pb0,
        M_AXI_AWREADY => s_axi_int_awready_pb0,
        M_AXI_WDATA => s_axi_int_wdata_pb0,
        M_AXI_WSTRB => s_axi_int_wstrb_pb0,
        M_AXI_WLAST => s_axi_int_wlast_pb0,
        M_AXI_WVALID => s_axi_int_wvalid_pb0,
        M_AXI_WREADY => s_axi_int_wready_pb0,
        M_AXI_BRESP => s_axi_int_bresp_pb0,
        M_AXI_BVALID => s_axi_int_bvalid_pb0,
        M_AXI_BREADY => s_axi_int_bready_pb0,
        M_AXI_ARADDR => s_axi_int_araddr_pb0,
        M_AXI_ARLEN => s_axi_int_arlen_pb0,
        M_AXI_ARSIZE => s_axi_int_arsize_pb0,
        M_AXI_ARBURST => s_axi_int_arburst_pb0,
        M_AXI_ARVALID => s_axi_int_arvalid_pb0,
        M_AXI_ARREADY => s_axi_int_arready_pb0,
        M_AXI_RDATA => s_axi_int_rdata_pb0,
        M_AXI_RRESP => s_axi_int_rresp_pb0,
        M_AXI_RLAST => s_axi_int_rlast_pb0,
        M_AXI_RVALID => s_axi_int_rvalid_pb0,
        M_AXI_RREADY => s_axi_int_rready_pb0

  );

  builder2: packet_builder2
  generic map (

    C_M_AXI_DATA_WIDTH => DATA_WIDTH,
    C_M_AXI_ADDR_WIDTH => ADDR_WIDTH,
    C_M_AXI_BURST_LEN => BURST_LEN
  ) 
  port map(
        ext_irq => (others => '0'),
        int_irq => (others => '0'),

        -- FIXME Delete Users ports 

        AXI_BASE_ADDRESS_I => AXI_BASE_ADDRESS_I_PB1,  
        AXI_WRITE_ADDRESS_I => AXI_WRITE_ADDRESS_I_PB1,
        AXI_WRITE_INIT_I => AXI_WRITE_INIT_I_PB1,    
        AXI_WRITE_DATA_I => AXI_WRITE_DATA_I_PB1,
        AXI_WRITE_VLD_I => AXI_WRITE_VLD_I_PB1,
        AXI_WRITE_RDY_O => AXI_WRITE_RDY_O_PB1,
        AXI_WRITE_DONE_O => AXI_WRITE_DONE_O_PB1,
        AXI_READ_ADDRESS_I => AXI_READ_ADDRESS_I_PB1,
        AXI_READ_INIT_I => AXI_READ_INIT_I_PB1,
        AXI_READ_DATA_O => AXI_READ_DATA_O_PB1,
        AXI_READ_VLD_O => AXI_READ_VLD_O_PB1,
        AXI_READ_RDY_I => AXI_READ_RDY_I_PB1,
        AXI_READ_LAST_O => AXI_READ_LAST_O_PB1,

        M_AXI_ACLK => clk,
        M_AXI_ARESETN => reset,

        M_AXI_AWADDR => s_axi_int_awaddr_pb1,
        M_AXI_AWLEN => s_axi_int_awlen_pb1,
        M_AXI_AWSIZE => s_axi_int_awsize_pb1,
        M_AXI_AWBURST => s_axi_int_awburst_pb1,
        M_AXI_AWVALID => s_axi_int_awvalid_pb1,
        M_AXI_AWREADY => s_axi_int_awready_pb1,
        M_AXI_WDATA => s_axi_int_wdata_pb1,
        M_AXI_WSTRB => s_axi_int_wstrb_pb1,
        M_AXI_WLAST => s_axi_int_wlast_pb1,
        M_AXI_WVALID => s_axi_int_wvalid_pb1,
        M_AXI_WREADY => s_axi_int_wready_pb1,
        M_AXI_BRESP => s_axi_int_bresp_pb1,
        M_AXI_BVALID => s_axi_int_bvalid_pb1,
        M_AXI_BREADY => s_axi_int_bready_pb1,
        M_AXI_ARADDR => s_axi_int_araddr_pb1,
        M_AXI_ARLEN => s_axi_int_arlen_pb1,
        M_AXI_ARSIZE => s_axi_int_arsize_pb1,
        M_AXI_ARBURST => s_axi_int_arburst_pb1,
        M_AXI_ARVALID => s_axi_int_arvalid_pb1,
        M_AXI_ARREADY => s_axi_int_arready_pb1,
        M_AXI_RDATA => s_axi_int_rdata_pb1,
        M_AXI_RRESP => s_axi_int_rresp_pb1,
        M_AXI_RLAST => s_axi_int_rlast_pb1,
        M_AXI_RVALID => s_axi_int_rvalid_pb1,
        M_AXI_RREADY => s_axi_int_rready_pb1

  );

  parser: packet_parser
  generic map (

    C_M_AXI_DATA_WIDTH => DATA_WIDTH,
    C_M_AXI_ADDR_WIDTH => ADDR_WIDTH,
    C_M_AXI_BURST_LEN => BURST_LEN
  ) 
  port map(
        ext_irq => (others => '0'),
        int_irq => (others => '0'),

        -- FIXME Delete Users ports 

        AXI_BASE_ADDRESS_I => AXI_BASE_ADDRESS_I_PP,  
        AXI_WRITE_ADDRESS_I => AXI_WRITE_ADDRESS_I_PP,
        AXI_WRITE_INIT_I => AXI_WRITE_INIT_I_PP,    
        AXI_WRITE_DATA_I => AXI_WRITE_DATA_I_PP,
        AXI_WRITE_VLD_I => AXI_WRITE_VLD_I_PP,
        AXI_WRITE_RDY_O => AXI_WRITE_RDY_O_PP,
        AXI_WRITE_DONE_O => AXI_WRITE_DONE_O_PP,
        AXI_READ_ADDRESS_I => AXI_READ_ADDRESS_I_PP,
        AXI_READ_INIT_I => AXI_READ_INIT_I_PP,
        AXI_READ_DATA_O => AXI_READ_DATA_O_PP,
        AXI_READ_VLD_O => AXI_READ_VLD_O_PP,
        AXI_READ_RDY_I => AXI_READ_RDY_I_PP,
        AXI_READ_LAST_O => AXI_READ_LAST_O_PP,

        M_AXI_ACLK => clk,
        M_AXI_ARESETN => reset,

        M_AXI_AWADDR => s_axi_int_awaddr_pp,
        M_AXI_AWLEN => s_axi_int_awlen_pp,
        M_AXI_AWSIZE => s_axi_int_awsize_pp,
        M_AXI_AWBURST => s_axi_int_awburst_pp,
        M_AXI_AWVALID => s_axi_int_awvalid_pp,
        M_AXI_AWREADY => s_axi_int_awready_pp,
        M_AXI_WDATA => s_axi_int_wdata_pp,
        M_AXI_WSTRB => s_axi_int_wstrb_pp,
        M_AXI_WLAST => s_axi_int_wlast_pp,
        M_AXI_WVALID => s_axi_int_wvalid_pp,
        M_AXI_WREADY => s_axi_int_wready_pp,
        M_AXI_BRESP => s_axi_int_bresp_pp,
        M_AXI_BVALID => s_axi_int_bvalid_pp,
        M_AXI_BREADY => s_axi_int_bready_pp,
        M_AXI_ARADDR => s_axi_int_araddr_pp,
        M_AXI_ARLEN => s_axi_int_arlen_pp,
        M_AXI_ARSIZE => s_axi_int_arsize_pp,
        M_AXI_ARBURST => s_axi_int_arburst_pp,
        M_AXI_ARVALID => s_axi_int_arvalid_pp,
        M_AXI_ARREADY => s_axi_int_arready_pp,
        M_AXI_RDATA => s_axi_int_rdata_pp,
        M_AXI_RRESP => s_axi_int_rresp_pp,
        M_AXI_RLAST => s_axi_int_rlast_pp,
        M_AXI_RVALID => s_axi_int_rvalid_pp,
        M_AXI_RREADY => s_axi_int_rready_pp

  );

  inmem: incomming_data_memory
  generic map(
    C_S_AXI_DATA_WIDTH => DATA_WIDTH,
    C_S_AXI_ADDR_WIDTH => ADDR_WIDTH
  ) 

  port map(
		S_AXI_ACLK => clk,
		S_AXI_ARESETN => reset,

		S_AXI_AWADDR => m_axi_int_awaddr_inmem,
		S_AXI_AWLEN => m_axi_int_awlen_inmem,
		S_AXI_AWSIZE => m_axi_int_awsize_inmem,
		S_AXI_AWBURST => m_axi_int_awburst_inmem,
		S_AXI_AWVALID => m_axi_int_awvalid_inmem,
		S_AXI_AWREADY => m_axi_int_awready_inmem,
		S_AXI_WDATA => m_axi_int_wdata_inmem,
		S_AXI_WSTRB => m_axi_int_wstrb_inmem,
		S_AXI_WLAST => m_axi_int_wlast_inmem,
		S_AXI_WVALID => m_axi_int_wvalid_inmem,
		S_AXI_WREADY => m_axi_int_wready_inmem,
		S_AXI_BRESP => m_axi_int_bresp_inmem,
		S_AXI_BVALID => m_axi_int_bvalid_inmem,
		S_AXI_BREADY => m_axi_int_bready_inmem,
		S_AXI_ARADDR => m_axi_int_araddr_inmem,
		S_AXI_ARLEN => m_axi_int_arlen_inmem,
		S_AXI_ARSIZE => m_axi_int_arsize_inmem,
		S_AXI_ARBURST => m_axi_int_arburst_inmem,
		S_AXI_ARVALID => m_axi_int_arvalid_inmem,
		S_AXI_ARREADY => m_axi_int_arready_inmem,
		S_AXI_RDATA => m_axi_int_rdata_inmem,
		S_AXI_RRESP => m_axi_int_rresp_inmem,
		S_AXI_RLAST => m_axi_int_rlast_inmem,
		S_AXI_RVALID => m_axi_int_rvalid_inmem,
		S_AXI_RREADY => m_axi_int_rready_inmem

  );

  outmem: outgoing_data_memory
  generic map(
    C_S_AXI_DATA_WIDTH => DATA_WIDTH,
    C_S_AXI_ADDR_WIDTH => ADDR_WIDTH
  ) 

  port map(
		S_AXI_ACLK => clk,
		S_AXI_ARESETN => reset,

		S_AXI_AWADDR => m_axi_int_awaddr_outmem,
		S_AXI_AWLEN => m_axi_int_awlen_outmem,
		S_AXI_AWSIZE => m_axi_int_awsize_outmem,
		S_AXI_AWBURST => m_axi_int_awburst_outmem,
		S_AXI_AWVALID => m_axi_int_awvalid_outmem,
		S_AXI_AWREADY => m_axi_int_awready_outmem,
		S_AXI_WDATA => m_axi_int_wdata_outmem,
		S_AXI_WSTRB => m_axi_int_wstrb_outmem,
		S_AXI_WLAST => m_axi_int_wlast_outmem,
		S_AXI_WVALID => m_axi_int_wvalid_outmem,
		S_AXI_WREADY => m_axi_int_wready_outmem,
		S_AXI_BRESP => m_axi_int_bresp_outmem,
		S_AXI_BVALID => m_axi_int_bvalid_outmem,
		S_AXI_BREADY => m_axi_int_bready_outmem,
		S_AXI_ARADDR => m_axi_int_araddr_outmem,
		S_AXI_ARLEN => m_axi_int_arlen_outmem,
		S_AXI_ARSIZE => m_axi_int_arsize_outmem,
		S_AXI_ARBURST => m_axi_int_arburst_outmem,
		S_AXI_ARVALID => m_axi_int_arvalid_outmem,
		S_AXI_ARREADY => m_axi_int_arready_outmem,
		S_AXI_RDATA => m_axi_int_rdata_outmem,
		S_AXI_RRESP => m_axi_int_rresp_outmem,
		S_AXI_RLAST => m_axi_int_rlast_outmem,
		S_AXI_RVALID => m_axi_int_rvalid_outmem,
		S_AXI_RREADY => m_axi_int_rready_outmem

  );

  system_regs: regs
  generic map(
    C_S_AXI_DATA_WIDTH => DATA_WIDTH,
    C_S_AXI_ADDR_WIDTH => ADDR_WIDTH
  ) 

  port map(
		S_AXI_ACLK => clk,
		S_AXI_ARESETN => reset,

		S_AXI_AWADDR => m_axi_int_awaddr_reg,
		-- S_AXI_AWLEN => m_axi_int_awlen_reg,
		-- S_AXI_AWSIZE => m_axi_int_awsize_reg,
		-- S_AXI_AWBURST => m_axi_int_awburst_reg,
		S_AXI_AWVALID => m_axi_int_awvalid_reg,
		S_AXI_AWREADY => m_axi_int_awready_reg,

		S_AXI_WDATA => m_axi_int_wdata_reg,
		S_AXI_WSTRB => m_axi_int_wstrb_reg,
		-- S_AXI_WLAST => m_axi_int_wlast_reg,
		S_AXI_WVALID => m_axi_int_wvalid_reg,
		S_AXI_WREADY => m_axi_int_wready_reg,

		S_AXI_BRESP => m_axi_int_bresp_reg,
		S_AXI_BVALID => m_axi_int_bvalid_reg,
		S_AXI_BREADY => m_axi_int_bready_reg,

		S_AXI_ARADDR => m_axi_int_araddr_reg,
		-- S_AXI_ARLEN => m_axi_int_arlen_reg,
		-- S_AXI_ARSIZE => m_axi_int_arsize_reg,
		-- S_AXI_ARBURST => m_axi_int_arburst_reg,
		S_AXI_ARVALID => m_axi_int_arvalid_reg,
		S_AXI_ARREADY => m_axi_int_arready_reg,

		S_AXI_RDATA => m_axi_int_rdata_reg,
		S_AXI_RRESP => m_axi_int_rresp_reg,
		-- S_AXI_RLAST => m_axi_int_rlast_reg,
		S_AXI_RVALID => m_axi_int_rvalid_reg,
		S_AXI_RREADY => m_axi_int_rready_reg

  );

  exreg: external_regs
  generic map(
    C_S_AXI_DATA_WIDTH => DATA_WIDTH,
    C_S_AXI_ADDR_WIDTH => ADDR_WIDTH
  ) 

  port map(
		S_AXI_ACLK => clk,
		S_AXI_ARESETN => reset,

		S_AXI_AWADDR => m_axi_int_awaddr_exreg,
		-- S_AXI_AWLEN => m_axi_int_awlen_exreg,
		-- S_AXI_AWSIZE => m_axi_int_awsize_exreg,
		-- S_AXI_AWBURST => m_axi_int_awburst_exreg,
		S_AXI_AWVALID => m_axi_int_awvalid_exreg,
		S_AXI_AWREADY => m_axi_int_awready_exreg,

		S_AXI_WDATA => m_axi_int_wdata_exreg,
		S_AXI_WSTRB => m_axi_int_wstrb_exreg,
		-- S_AXI_WLAST => m_axi_int_wlast_exreg,
		S_AXI_WVALID => m_axi_int_wvalid_exreg,
		S_AXI_WREADY => m_axi_int_wready_exreg,

		S_AXI_BRESP => m_axi_int_bresp_exreg,
		S_AXI_BVALID => m_axi_int_bvalid_exreg,
		S_AXI_BREADY => m_axi_int_bready_exreg,

		S_AXI_ARADDR => m_axi_int_araddr_exreg,
		-- S_AXI_ARLEN => m_axi_int_arlen_exreg,
		-- S_AXI_ARSIZE => m_axi_int_arsize_exreg,
		-- S_AXI_ARBURST => m_axi_int_arburst_exreg,
		S_AXI_ARVALID => m_axi_int_arvalid_exreg,
		S_AXI_ARREADY => m_axi_int_arready_exreg,
		S_AXI_RDATA => m_axi_int_rdata_exreg,
		S_AXI_RRESP => m_axi_int_rresp_exreg,
		-- S_AXI_RLAST => m_axi_int_rlast_exreg,
		S_AXI_RVALID => m_axi_int_rvalid_exreg,
		S_AXI_RREADY => m_axi_int_rready_exreg

  );
end architecture;
