----------------------------------------------------------------------------------
-- Company: 
-- Engineer: Aleksa Djokovic
-- 
-- Create Date: 07/03/2023 12:24:22 PM
-- Design Name: Packet processing interconnect
-- Module Name: interconnect - Behavioral
-- Project Name: 
-- Target Devices: 
-- Tool Versions: 
-- Description: 
-- 
-- Dependencies: 
-- 
-- Revision:
-- Revision 0.01 - File Created
-- Additional Comments:
-- 
----------------------------------------------------------------------------------


library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

-- Uncomment the following library declaration if using
-- arithmetic functions with Signed or Unsigned values
--use IEEE.NUMERIC_STD.ALL;

-- Uncomment the following library declaration if instantiating
-- any Xilinx leaf cells in this code.
--library UNISIM;
--use UNISIM.VComponents.all;

entity interconnect is
	generic (
		C_M_AXI_DATA_WIDTH	: integer	:= 32;
		C_M_AXI_ADDR_WIDTH	: integer	:= 32
	);
	port (
        --------------------------------------------------------------------------------
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
end interconnect;

architecture Behavioral of interconnect is

	-- Round robin arbitration logic
	component arbiter_rr is
		port (
			clk: 		in std_logic;
			rstn: 	in std_logic;

			busy: in std_logic;
			req:		in std_logic_vector;
			gnt:		out std_logic_vector
		);
	end component;
	-- Busy logic generator, 3 states -> AVAILABLE, BUSY_WRITE, BUSY_READ
	component int_fsm is
	port (
	    clk : in std_logic;
	    reset : in std_logic;

	    awvalid : in std_logic;
	    bvalid : in std_logic;
	    bready : in std_logic;

	    arvalid : in std_logic;
	    rlast : in std_logic;
	    rvalid : in std_logic;
	    rready : in std_logic;
	    arlen : in std_logic_vector(7 downto 0);

	    busy : out std_logic
	);
	end component;

	-- REQ signals
	signal ctrl_req : std_logic;
	signal pb0_req : std_logic;
	signal pb1_req : std_logic;
	signal pp_req : std_logic;

	signal req : std_logic_vector(3 downto 0);
	signal gnt : std_logic_vector(3 downto 0);

	-- BUSY, when the master is connected to internal AXI4 signals, busy is asserted high when any ov the valid signals of the corresponding master are high
	signal int_busy: std_logic;

	-- AXI4 interconnect internal signals
	-- ADDRESS WRITE CHANNEL
	signal int_awaddr: std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
	signal int_awlen: std_logic_vector(7 downto 0);
	signal int_awsize: std_logic_vector(2 downto 0);
	signal int_awburst: std_logic_vector(1 downto 0);

	signal int_awvalid: std_logic;
	signal int_awready: std_logic;

	-- WRITE DATA CHANNEL
	signal int_wdata: std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
	signal int_wstrb: std_logic_vector(C_M_AXI_DATA_WIDTH/8-1 downto 0);
	signal int_wlast: std_logic;

	signal int_wvalid: std_logic;
	signal int_wready: std_logic;

	-- WRITE RESPONSE CHANNEL
	signal int_bresp: std_logic_vector(1 downto 0);
	signal int_bvalid: std_logic;
	signal int_bready: std_logic;

	-- READ ADDRESS CHANNEL
	signal int_araddr: std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
	signal int_arlen: std_logic_vector(7 downto 0);
	signal int_arsize: std_logic_vector(2 downto 0);
	signal int_arburst: std_logic_vector(1 downto 0);

	signal int_arvalid: std_logic;
	signal int_arready: std_logic;

	-- READ DATA CHANNEL
	signal int_rdata: std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
	signal int_rresp: std_logic_vector(1 downto 0);
	signal int_rlast: std_logic;

	signal int_rvalid: std_logic;
	signal int_rready: std_logic;

	-- WRITE ADDRESS DECODER
	signal aw_valid_dec : std_logic_vector(1 downto 0);
	
	-- READ ADDRESS DECODER
	signal ar_valid_dec : std_logic_vector(1 downto 0);

begin

	----------------------------------------------------------------------------------------------------------------------------------------------------------------	
	-- FROM MASTER TO SLAVE

	-- Each channel in interconnect for each master has input and output signals. Looking from intcon to master's side, input signals in intcon will be lead to mux
	-- where the master with the grant will be chosen. Those signals are than lead to all slaves directly except control valid signal which goes to demux.
	-- Based on address decoder corresponding slave valid signal will be connected to demux input where all others demux outputs also connected to other slaves will
	-- get the value 0.

	-- FROM SLAVE TO MASTER

	-- Similar logic must be added for slave ready control signal, just in opposite way. Slave's ready signal is lead to mux selected by decoder. Mux output is lead
	-- to demux selected by arbiter's gnt signal.

	----------------------------------------------------------------------------------------------------------------------------------------------------------------	

	-- meybe should be or with wvalid signals?
  -- BUG only write transaction were eligeble to make reqests
	ctrl_req <= s_axi_int_awvalid_ctrl or s_axi_int_arvalid_ctrl;
	pb0_req <= s_axi_int_awvalid_pb0 or s_axi_int_arvalid_pb0;
	pb1_req <= s_axi_int_awvalid_pb1 or s_axi_int_arvalid_pb1;
	pp_req <= s_axi_int_awvalid_pp or s_axi_int_arvalid_pp;

	-- Round robbin arbiter input req signal
	req(0) <= ctrl_req;
	req(1) <= pb0_req;
	req(2) <= pb1_req;
	req(3) <= pp_req;

	-- Connect grant signals to Master's ready
	-- s_axi_int_awready_ctrl <= gnt(0);
	-- s_axi_int_awready_pb0 <= gnt(1);
	-- s_axi_int_awready_pb1 <= gnt(2);
	-- s_axi_int_awready_pp <= gnt(3);


	--------------------------------------------------------------------------------
	-- WRITE ADDRESS DECODER 
	--------------------------------------------------------------------------------
	aw_dec: process(int_awaddr) 
	begin
		case(int_awaddr((C_M_AXI_ADDR_WIDTH-1) - 8 downto C_M_AXI_ADDR_WIDTH - 16)) is 
			when x"00" =>
				aw_valid_dec <= "00";
			when x"01" =>
				aw_valid_dec <= "01";
			when x"10" =>
				aw_valid_dec <= "10";
			-- when x"20" =>
			when others =>
				aw_valid_dec <= "11";
				-- assert false report "Invalid address value in write address decoder" severity error;
		end case;
	end process;
	--------------------------------------------------------------------------------

	--------------------------------------------------------------------------------
	-- READ ADDRESS DECODER 
	
	--------------------------------------------------------------------------------
	ar_dec: process(int_araddr) 
	begin
		case(int_araddr((C_M_AXI_ADDR_WIDTH-1) - 8 downto C_M_AXI_ADDR_WIDTH - 16)) is 
			when x"00" =>
				ar_valid_dec <= "00";
			when x"01" =>
				ar_valid_dec <= "01";
			when x"10" =>
				ar_valid_dec <= "10";
			-- when x"20" =>
			when others =>
				ar_valid_dec <= "11";
				-- assert false report "Invalid address value in read address decoder" severity error;
		end case;
	end process;
	--------------------------------------------------------------------------------

	--------------------------------------------------------------------------------
	-- ADDRESS WRITE CHANNEL LOGIC
	--------------------------------------------------------------------------------

	aw_mux_gnt : process(
					 s_axi_int_awaddr_ctrl, s_axi_int_awaddr_pb0, s_axi_int_awaddr_pb1, s_axi_int_awaddr_pp,
					 s_axi_int_awlen_ctrl, s_axi_int_awlen_pb0, s_axi_int_awlen_pb1, s_axi_int_awlen_pp,
					 s_axi_int_awsize_ctrl, s_axi_int_awsize_pb0, s_axi_int_awsize_pb1, s_axi_int_awsize_pp,
					 s_axi_int_awburst_ctrl, s_axi_int_awburst_pb0, s_axi_int_awburst_pb1, s_axi_int_awburst_pp,
					 s_axi_int_awvalid_ctrl, s_axi_int_awvalid_pb0, s_axi_int_awvalid_pb1, s_axi_int_awvalid_pp,
					 gnt
	)
	begin
		case(gnt) is 

		-- // BUG When 0000 then pp module is enabled
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				int_awaddr <= s_axi_int_awaddr_ctrl;
				int_awlen <= s_axi_int_awlen_ctrl;
				int_awsize <= s_axi_int_awsize_ctrl;
				int_awburst <= s_axi_int_awburst_ctrl;
				int_awvalid <= s_axi_int_awvalid_ctrl;
			when "0010" =>
				int_awaddr <= s_axi_int_awaddr_pb0;
				int_awlen <= s_axi_int_awlen_pb0;
				int_awsize <= s_axi_int_awsize_pb0;
				int_awburst <= s_axi_int_awburst_pb0;
				int_awvalid <= s_axi_int_awvalid_pb0;
			when "0100" =>
				int_awaddr <= s_axi_int_awaddr_pb1;
				int_awlen <= s_axi_int_awlen_pb1;
				int_awsize <= s_axi_int_awsize_pb1;
				int_awburst <= s_axi_int_awburst_pb1;
				int_awvalid <= s_axi_int_awvalid_pb1;
			when "1000" =>
				int_awaddr <= s_axi_int_awaddr_pp;
				int_awlen <= s_axi_int_awlen_pp;
				int_awsize <= s_axi_int_awsize_pp;
				int_awburst <= s_axi_int_awburst_pp;
				int_awvalid <= s_axi_int_awvalid_pp;
			when others =>
				int_awaddr <= (others => '0');
				int_awlen <= (others => '0');
				int_awsize <= (others => '0');
				int_awburst <= (others => '0') ;
				int_awvalid <= '0';
		end case;
	
	end process;

	-- assign all internal signal directly to all slaves
	m_axi_int_awaddr_inmem <= int_awaddr;
	m_axi_int_awlen_inmem <= int_awlen;
	m_axi_int_awsize_inmem <= int_awsize;
	m_axi_int_awburst_inmem <= int_awburst;

	m_axi_int_awaddr_outmem <= int_awaddr;
	m_axi_int_awlen_outmem <= int_awlen;
	m_axi_int_awsize_outmem <= int_awsize;
	m_axi_int_awburst_outmem <= int_awburst;

	m_axi_int_awaddr_reg <= int_awaddr;
	m_axi_int_awlen_reg <= int_awlen;
	m_axi_int_awsize_reg <= int_awsize;
	m_axi_int_awburst_reg <= int_awburst;

	m_axi_int_awaddr_exreg <= int_awaddr;
	m_axi_int_awlen_exreg <= int_awlen;
	m_axi_int_awsize_exreg <= int_awsize;
	m_axi_int_awburst_exreg <= int_awburst;

	awvalid_demux_dec : process (int_awvalid, aw_valid_dec)
	begin
		m_axi_int_awvalid_inmem <= '0';
		m_axi_int_awvalid_outmem <= '0';
		m_axi_int_awvalid_reg <= '0';
		m_axi_int_awvalid_exreg <= '0';
		case(aw_valid_dec) is 
			when "00" =>
				m_axi_int_awvalid_inmem <= int_awvalid;
			when "01" =>
				m_axi_int_awvalid_outmem <= int_awvalid;
			when "10" =>
				m_axi_int_awvalid_reg <= int_awvalid;
			-- when "11" =>
			when others =>
				m_axi_int_awvalid_exreg <= int_awvalid;
				-- assert false report "Invalid aw_valid_dec value" severity error;
		end case;
	end process;

	awready_mux_dec : process (m_axi_int_awready_inmem, m_axi_int_awready_outmem,
														 m_axi_int_awready_reg, m_axi_int_awready_exreg, aw_valid_dec)
	begin
		case(aw_valid_dec) is 
			when "00" =>
				int_awready <= m_axi_int_awready_inmem;
			when "01" =>
				int_awready <= m_axi_int_awready_outmem;
			when "10" =>
				int_awready <= m_axi_int_awready_reg;
			-- when "11" =>
			when others =>
				int_awready <= m_axi_int_awready_exreg;
				-- assert false report "Invalid aw_valid_dec value" severity error;
		end case;
	end process;

	awready_demux_gnt : process (int_awready, gnt)
	begin 
		s_axi_int_awready_ctrl <= '0';
		s_axi_int_awready_pb0 <= '0';
		s_axi_int_awready_pb1 <= '0';
		s_axi_int_awready_pp <= '0';

		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				s_axi_int_awready_ctrl <= int_awready;
			when "0010" =>
				s_axi_int_awready_pb0 <= int_awready;
			when "0100" =>
				s_axi_int_awready_pb1 <= int_awready;
			when "1000" =>
				s_axi_int_awready_pp <= int_awready;
			when others =>
				s_axi_int_awready_ctrl <= '0';
				s_axi_int_awready_pb0 <= '0';
				s_axi_int_awready_pb1 <= '0';
				s_axi_int_awready_pp <= '0';
		end case;
	end process;

	--------------------------------------------------------------------------------

	--------------------------------------------------------------------------------
	-- WRITE CHANNEL LOGIC
	--------------------------------------------------------------------------------
	w_mux : process(
					s_axi_int_wdata_ctrl, s_axi_int_wdata_pb0, s_axi_int_wdata_pb1, s_axi_int_wdata_pp,
					s_axi_int_wstrb_ctrl, s_axi_int_wstrb_pb0, s_axi_int_wstrb_pb1, s_axi_int_wstrb_pp,
					s_axi_int_wlast_ctrl, s_axi_int_wlast_pb0, s_axi_int_wlast_pb1, s_axi_int_wlast_pp,
					s_axi_int_wvalid_ctrl, s_axi_int_wvalid_pb0, s_axi_int_wvalid_pb1, s_axi_int_wvalid_pp,
					gnt
					)
	begin 
		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				int_wdata <= s_axi_int_wdata_ctrl;
				int_wstrb <= s_axi_int_wstrb_ctrl; 
				int_wlast <= s_axi_int_wlast_ctrl; 
				int_wvalid <= s_axi_int_wvalid_ctrl;
			when "0010" =>
				int_wdata <= s_axi_int_wdata_pb0;
				int_wstrb <= s_axi_int_wstrb_pb0; 
				int_wlast <= s_axi_int_wlast_pb0; 
				int_wvalid <= s_axi_int_wvalid_pb0;
			when "0100" =>
				int_wdata <= s_axi_int_wdata_pb1;
				int_wstrb <= s_axi_int_wstrb_pb1; 
				int_wlast <= s_axi_int_wlast_pb1; 
				int_wvalid <= s_axi_int_wvalid_pb1;
			when "1000" =>
				int_wdata <= s_axi_int_wdata_pp;
				int_wstrb <= s_axi_int_wstrb_pp; 
				int_wlast <= s_axi_int_wlast_pp; 
				int_wvalid <= s_axi_int_wvalid_pp;
			when others =>
				int_wdata <= (others => '0');
				int_wstrb <= (others => '0'); 
				int_wlast <= '0'; 
				int_wvalid <= '0';
		end case;
	end process;

	-- assign all internal signal directly to all slaves
	m_axi_int_wdata_inmem <= int_wdata;
	m_axi_int_wstrb_inmem <= int_wstrb;
	m_axi_int_wlast_inmem <= int_wlast;

	m_axi_int_wdata_outmem <= int_wdata;
	m_axi_int_wstrb_outmem <= int_wstrb;
	m_axi_int_wlast_outmem <= int_wlast;
	
	m_axi_int_wdata_reg <= int_wdata;
	m_axi_int_wstrb_reg <= int_wstrb;
	m_axi_int_wlast_reg <= int_wlast;

	m_axi_int_wdata_exreg <= int_wdata;
	m_axi_int_wstrb_exreg <= int_wstrb;
	m_axi_int_wlast_exreg <= int_wlast;

	wvalid_demux_dec : process (int_wvalid, aw_valid_dec)
	begin
		m_axi_int_wvalid_inmem <= '0';
		m_axi_int_wvalid_outmem <= '0';
		m_axi_int_wvalid_reg <= '0';
		m_axi_int_wvalid_exreg <= '0';
		case(aw_valid_dec) is 
			when "00" =>
				m_axi_int_wvalid_inmem <= int_wvalid;
			when "01" =>
				m_axi_int_wvalid_outmem <= int_wvalid;
			when "10" =>
				m_axi_int_wvalid_reg <= int_wvalid;
			-- when "11" =>
			when others =>
				m_axi_int_wvalid_exreg <= int_wvalid;
				-- assert false report "Invalid aw_valid_dec value" severity error;
		end case;
	end process;

	wvalid_mux_dec : process (m_axi_int_wready_inmem, m_axi_int_wready_outmem,
														 m_axi_int_wready_reg, m_axi_int_wready_exreg, aw_valid_dec)
	begin
		case(aw_valid_dec) is 
			when "00" =>
				int_wready <= m_axi_int_wready_inmem;
			when "01" =>
				int_wready <= m_axi_int_wready_outmem;
			when "10" =>
				int_wready <= m_axi_int_wready_reg;
			-- when "11" =>
			when others =>
				int_wready <= m_axi_int_wready_exreg;
				-- assert false report "Invalid aw_valid_dec value" severity error;
		end case;
	end process;

	wready_demux_gnt : process (int_wready, gnt)
	begin 
		s_axi_int_wready_ctrl <= '0';
		s_axi_int_wready_pb0 <= '0';
  s_axi_int_wready_pb1 <= '0';
  s_axi_int_wready_pp <= '0';

		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				s_axi_int_wready_ctrl <= int_wready;
			when "0010" =>
				s_axi_int_wready_pb0 <= int_wready;
			when "0100" =>
				s_axi_int_wready_pb1 <= int_wready;
			when "1000" =>
				s_axi_int_wready_pp <= int_wready;
			when others =>
				-- default
				s_axi_int_wready_ctrl <= '0';
				s_axi_int_wready_pb0 <= '0';
				s_axi_int_wready_pb1 <= '0';
				s_axi_int_wready_pp <= '0';
		end case;
	end process;
	--------------------------------------------------------------------------------

	--------------------------------------------------------------------------------
	-- WRITE RESPONSE LOGIC
	--------------------------------------------------------------------------------
	b_mux : process(
					m_axi_int_bresp_inmem, m_axi_int_bresp_outmem, m_axi_int_bresp_reg, m_axi_int_bresp_exreg,
					m_axi_int_bvalid_inmem, m_axi_int_bvalid_outmem, m_axi_int_bvalid_reg, m_axi_int_bvalid_exreg, 
					ar_valid_dec
					)
	begin 
		case(ar_valid_dec) is 
			when "00" =>
				int_bresp <= m_axi_int_bresp_inmem;
				int_bvalid <= m_axi_int_bvalid_inmem;
				-- int_bready <= s_axi_int_bready_ctrl;

			when "01" =>
				int_bresp <= m_axi_int_bresp_outmem;
				int_bvalid <= m_axi_int_bvalid_outmem;
				-- int_bready <= s_axi_int_bready_pb0;
			when "10" =>
				int_bresp <= m_axi_int_bresp_reg;
				int_bvalid <= m_axi_int_bvalid_reg;
				-- int_bready <= s_axi_int_bready_pb1;
			-- when "11" =>
				-- int_bready <= s_axi_int_bready_pp;
			when others =>
				int_bresp <= m_axi_int_bresp_exreg;
				int_bvalid <= m_axi_int_bvalid_exreg;
				-- assert false report "Invalid gnt value" severity error;
		end case;
	end process;

	s_axi_int_bresp_ctrl <= int_bresp;
	s_axi_int_bresp_pb0 <= int_bresp;
	s_axi_int_bresp_pb1 <= int_bresp;
	s_axi_int_bresp_pp <= int_bresp;

	bvalid_demux_gnt : process (int_bvalid, gnt)
	begin 
		s_axi_int_bvalid_ctrl <= '0';
		s_axi_int_bvalid_pb0 <= '0';
		s_axi_int_bvalid_pb1 <= '0';
		s_axi_int_bvalid_pp <= '0';

		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				s_axi_int_bvalid_ctrl <= int_bvalid;
			when "0010" =>
				s_axi_int_bvalid_pb0 <= int_bvalid;
			when "0100" =>
				s_axi_int_bvalid_pb1 <= int_bvalid;
			when "1000" =>
				s_axi_int_bvalid_pp <= int_bvalid;
			when others =>
				-- default
				s_axi_int_bvalid_ctrl <= '0';
				s_axi_int_bvalid_pb0 <= '0';
				s_axi_int_bvalid_pb1 <= '0';
				s_axi_int_bvalid_pp <= '0';
		end case;
	end process;

	bready_mux_gnt : process(
					s_axi_int_bready_ctrl, s_axi_int_bready_pb0, s_axi_int_bready_pb1, s_axi_int_bready_pp,
					gnt
					)
	begin 
		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				int_bready <= s_axi_int_bready_ctrl;
			when "0010" =>
				int_bready <= s_axi_int_bready_pb0;
			when "0100" =>
				int_bready <= s_axi_int_bready_pb1;
			when "1000" =>
				int_bready <= s_axi_int_bready_pp;
			when others =>
				int_bready <= '0';
		end case;
	end process;

	bready_demux_dec : process(
					int_bready,
					ar_valid_dec
					)
	begin 

		m_axi_int_bready_inmem <= '0';
		m_axi_int_bready_outmem <= '0';
		m_axi_int_bready_reg <= '0';
		m_axi_int_bready_exreg <= '0';

		case(ar_valid_dec) is 
			when "00" =>
				m_axi_int_bready_inmem <= int_bready;
			when "01" =>
				m_axi_int_bready_outmem <= int_bready;
			when "10" =>
				m_axi_int_bready_reg <= int_bready;
			-- when "11" =>
			when others =>
				m_axi_int_bready_exreg <= int_bready;
		end case;
	end process;
	--------------------------------------------------------------------------------

	--------------------------------------------------------------------------------
	-- ADDRESS READ LOGIC
	--------------------------------------------------------------------------------
	ar_mux_gnt : process(
					 s_axi_int_araddr_ctrl, s_axi_int_araddr_pb0, s_axi_int_araddr_pb1, s_axi_int_araddr_pp,
					 s_axi_int_arlen_ctrl, s_axi_int_arlen_pb0, s_axi_int_arlen_pb1, s_axi_int_arlen_pp,
					 s_axi_int_arsize_ctrl, s_axi_int_arsize_pb0, s_axi_int_arsize_pb1, s_axi_int_arsize_pp,
					 s_axi_int_arburst_ctrl, s_axi_int_arburst_pb0, s_axi_int_arburst_pb1, s_axi_int_arburst_pp,
					 s_axi_int_arvalid_ctrl, s_axi_int_arvalid_pb0, s_axi_int_arvalid_pb1, s_axi_int_arvalid_pp,
					 gnt
	)
	begin
		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				int_araddr <= s_axi_int_araddr_ctrl;
				int_arlen <= s_axi_int_arlen_ctrl;
				int_arsize <= s_axi_int_arsize_ctrl;
				int_arburst <= s_axi_int_arburst_ctrl;
				int_arvalid <= s_axi_int_arvalid_ctrl;
			when "0010" =>
				int_araddr <= s_axi_int_araddr_pb0;
				int_arlen <= s_axi_int_arlen_pb0;
				int_arsize <= s_axi_int_arsize_pb0;
				int_arburst <= s_axi_int_arburst_pb0;
				int_arvalid <= s_axi_int_arvalid_pb0;
			when "0100" =>
				int_araddr <= s_axi_int_araddr_pb1;
				int_arlen <= s_axi_int_arlen_pb1;
				int_arsize <= s_axi_int_arsize_pb1;
				int_arburst <= s_axi_int_arburst_pb1;
				int_arvalid <= s_axi_int_arvalid_pb1;
			when "1000" =>
				int_araddr <= s_axi_int_araddr_pp;
				int_arlen <= s_axi_int_arlen_pp;
				int_arsize <= s_axi_int_arsize_pp;
				int_arburst <= s_axi_int_arburst_pp;
				int_arvalid <= s_axi_int_arvalid_pp;
			when others =>
				int_araddr <= (others => '0');
				int_arlen <= (others => '0');
				int_arsize <= (others => '0');
				int_arburst <= (others => '0');
				int_arvalid <= '0';
		end case;
	
	end process;

	m_axi_int_araddr_inmem <= int_araddr;
	m_axi_int_arlen_inmem <= int_arlen;
	m_axi_int_arsize_inmem <= int_arsize;
	m_axi_int_arburst_inmem <= int_arburst;

	m_axi_int_araddr_outmem <= int_araddr;
	m_axi_int_arlen_outmem <= int_arlen;
	m_axi_int_arsize_outmem <= int_arsize;
	m_axi_int_arburst_outmem <= int_arburst;

	m_axi_int_araddr_reg <= int_araddr;
	m_axi_int_arlen_reg <= int_arlen;
	m_axi_int_arsize_reg <= int_arsize;
	m_axi_int_arburst_reg <= int_arburst;

	m_axi_int_araddr_exreg <= int_araddr;
	m_axi_int_arlen_exreg <= int_arlen;
	m_axi_int_arsize_exreg <= int_arsize;
	m_axi_int_arburst_exreg <= int_arburst;

	arvalid_demux_dec : process (int_arvalid, ar_valid_dec)
	begin
		m_axi_int_arvalid_inmem <= '0';
		m_axi_int_arvalid_outmem <= '0';
		m_axi_int_arvalid_reg <= '0';
		m_axi_int_arvalid_exreg <= '0';
		case(ar_valid_dec) is 
			when "00" =>
				m_axi_int_arvalid_inmem <= int_arvalid;
			when "01" =>
				m_axi_int_arvalid_outmem <= int_arvalid;
			when "10" =>
				m_axi_int_arvalid_reg <= int_arvalid;
			-- when "11" =>
			when others =>
				m_axi_int_arvalid_exreg <= int_arvalid;
				-- assert false report "Invalid ar_valid_dec value" severity error;
		end case;
	end process;

	arready_mux_dec : process (m_axi_int_arready_inmem, m_axi_int_arready_outmem,
														 m_axi_int_arready_reg, m_axi_int_arready_exreg, ar_valid_dec)
	begin
		case(ar_valid_dec) is 
			when "00" =>
				int_arready <= m_axi_int_arready_inmem;
			when "01" =>
				int_arready <= m_axi_int_arready_outmem;
			when "10" =>
				int_arready <= m_axi_int_arready_reg;
			-- when "11" =>
			when others =>
				int_arready <= m_axi_int_arready_exreg;
				-- assert false report "Invalid ar_valid_dec value" severity error;
		end case;
	end process;

	arready_demux_gnt : process (int_arready, gnt)
	begin 

		s_axi_int_arready_ctrl <= '0';
		s_axi_int_arready_pb0 <= '0';
		s_axi_int_arready_pb1 <= '0';
		s_axi_int_arready_pp <= '0';
		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				s_axi_int_arready_ctrl <= int_arready;
			when "0010" =>
				s_axi_int_arready_pb0 <= int_arready;
			when "0100" =>
				s_axi_int_arready_pb1 <= int_arready;
			when "1000" =>
				s_axi_int_arready_pp <= int_arready;
			when others =>
				-- default
				s_axi_int_arready_ctrl <= '0';
				s_axi_int_arready_pb0 <= '0';
				s_axi_int_arready_pb1 <= '0';
				s_axi_int_arready_pp <= '0';
		end case;
	end process;
	--------------------------------------------------------------------------------

	--------------------------------------------------------------------------------
	-- READ LOGIC
	--------------------------------------------------------------------------------

	r_mux : process(
					m_axi_int_rdata_inmem, m_axi_int_rdata_outmem, m_axi_int_rdata_reg, m_axi_int_rdata_exreg,
					m_axi_int_rresp_inmem, m_axi_int_rresp_outmem, m_axi_int_rresp_reg, m_axi_int_rresp_exreg,
					m_axi_int_rlast_inmem, m_axi_int_rlast_outmem, m_axi_int_rlast_reg, m_axi_int_rlast_exreg,
					m_axi_int_rvalid_inmem, m_axi_int_rvalid_outmem, m_axi_int_rvalid_reg, m_axi_int_rvalid_exreg,
					ar_valid_dec
					)
	begin 
		case(ar_valid_dec) is 
			when "00" =>
				int_rdata <= m_axi_int_rdata_inmem;
				int_rresp <= m_axi_int_rresp_inmem;
				int_rlast <= m_axi_int_rlast_inmem;
				int_rvalid <= m_axi_int_rvalid_inmem;

			when "01" =>
				int_rdata <= m_axi_int_rdata_outmem;
				int_rresp <= m_axi_int_rresp_outmem;
				int_rlast <= m_axi_int_rlast_outmem;
				int_rvalid <= m_axi_int_rvalid_outmem;
			when "10" =>
				int_rdata <= m_axi_int_rdata_reg;
				int_rresp <= m_axi_int_rresp_reg;
				int_rlast <= m_axi_int_rlast_reg;
				int_rvalid <= m_axi_int_rvalid_reg;
			-- when "11" =>
			when others =>
				int_rdata <= m_axi_int_rdata_exreg;
				int_rresp <= m_axi_int_rresp_exreg;
				int_rlast <= m_axi_int_rlast_exreg;
				int_rvalid <= m_axi_int_rvalid_exreg;
				-- assert false report "Invalid gnt value" severity error;
		end case;
	end process;

	s_axi_int_rdata_ctrl <= int_rdata;
	s_axi_int_rresp_ctrl <= int_rresp;
	s_axi_int_rlast_ctrl <= int_rlast;

	s_axi_int_rdata_pb0 <= int_rdata;
	s_axi_int_rresp_pb0 <= int_rresp;
	s_axi_int_rlast_pb0 <= int_rlast;

	s_axi_int_rdata_pb1 <= int_rdata;
	s_axi_int_rresp_pb1 <= int_rresp;
	s_axi_int_rlast_pb1 <= int_rlast;

	s_axi_int_rdata_pp <= int_rdata;
	s_axi_int_rresp_pp <= int_rresp;
	s_axi_int_rlast_pp <= int_rlast;

	rvalid_demux_gnt : process (int_rvalid, gnt)
	begin 
		s_axi_int_rvalid_ctrl <= '0';
		s_axi_int_rvalid_pb0 <= '0';
		s_axi_int_rvalid_pb1 <= '0';
	 s_axi_int_rvalid_pp <= '0';

		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				s_axi_int_rvalid_ctrl <= int_rvalid;
			when "0010" =>
				s_axi_int_rvalid_pb0 <= int_rvalid;
			when "0100" =>
				s_axi_int_rvalid_pb1 <= int_rvalid;
			when "1000" =>
				s_axi_int_rvalid_pp <= int_rvalid;
			when others =>
				-- default
				s_axi_int_rvalid_ctrl <= '0';
				s_axi_int_rvalid_pb0 <= '0';
				s_axi_int_rvalid_pb1 <= '0';
				s_axi_int_rvalid_pp <= '0';
		end case;
	end process;

	-- FIX rlast stability bug 
	rlast_demux_gnt : process (int_rlast, gnt)
	begin 
		s_axi_int_rlast_ctrl <= '0';
		s_axi_int_rlast_pb0 <= '0';
		s_axi_int_rlast_pb1 <= '0';
	 s_axi_int_rlast_pp <= '0';

		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				s_axi_int_rlast_ctrl <= int_rlast;
			when "0010" =>
				s_axi_int_rlast_pb0 <= int_rlast;
			when "0100" =>
				s_axi_int_rlast_pb1 <= int_rlast;
			when "1000" =>
				s_axi_int_rlast_pp <= int_rlast;
			when others =>
				-- default
				s_axi_int_rlast_ctrl <= '0';
				s_axi_int_rlast_pb0 <= '0';
				s_axi_int_rlast_pb1 <= '0';
				s_axi_int_rlast_pp <= '0';
		end case;
	end process;

	rready_mux_gnt : process(
					s_axi_int_rready_ctrl, s_axi_int_rready_pb0, s_axi_int_rready_pb1, s_axi_int_rready_pp,
					gnt
					)
	begin 
		case(gnt) is 
		-- // [x] Fix gnt 0000 value
			when "0001" =>
				int_rready <= s_axi_int_rready_ctrl;
			when "0010" =>
				int_rready <= s_axi_int_rready_pb0;
			when "0100" =>
				int_rready <= s_axi_int_rready_pb1;
			when "1000" =>
				int_rready <= s_axi_int_rready_pp;
			when others =>
				int_rready <= '0';
		end case;
	end process;

	rready_demux_dec : process(
					int_rready,
					ar_valid_dec
					)
	begin 
		m_axi_int_rready_inmem <= '0';
		m_axi_int_rready_outmem <= '0';
		m_axi_int_rready_reg <= '0';
		m_axi_int_rready_exreg <= '0';

		case(ar_valid_dec) is 
			when "00" =>
				m_axi_int_rready_inmem <= int_rready;
			when "01" =>
				m_axi_int_rready_outmem <= int_rready;
			when "10" =>
				m_axi_int_rready_reg <= int_rready;
			-- when "11" =>
			when others =>
				m_axi_int_rready_exreg <= int_rready;
		end case;
	end process;
	--------------------------------------------------------------------------------

	arb_inst : arbiter_rr
	port map(
		clk  => clk,
		rstn => reset,
		busy => int_busy,

		req  => req,
		gnt  => gnt
	);

	fsm: int_fsm
	port map (
		clk => clk,
		reset => reset,
		awvalid => int_awvalid,
		bvalid => int_bvalid,
		bready => int_bready,
		arvalid => int_arvalid,
		rlast => int_rlast,
		rvalid => int_rvalid,
		rready => int_rready,
		arlen => int_arlen,
		busy => int_busy
	);


end Behavioral;
