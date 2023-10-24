
library ieee;
use ieee.std_logic_1164.all;
use IEEE.NUMERIC_STD.ALL;

entity controller is
    generic(
        C_M_AXI_ADDR_WIDTH	: integer	:= 32;
        C_M_AXI_DATA_WIDTH	: integer	:= 32
    );
    port (

        -- INTERRUPT PORTS
        ext_irq : in std_logic_vector(1 downto 0);
        --FIXME internal interrupt handling
        int_irq : in std_logic_vector(2 downto 0);
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
end entity controller;

architecture Behavioral of controller is


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

    signal axi_burst_len_s : std_logic_vector(7 downto 0);

    --  WRITE CHANNEL
    signal axi_write_init_reg, axi_write_init_next : std_logic;    --starts write transaction
    signal axi_write_data_s    : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
    signal axi_write_data_next, axi_write_data_reg    : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
    signal axi_write_vld_s     : std_logic;  --  indicates that write data is valid
    signal axi_write_rdy_s     : std_logic;  -- indicates that controler is ready to                                          -- accept data
    signal axi_write_done_s    : std_logic;  -- indicates that burst has finished

    -- READ CHANNEL

    signal axi_read_init_reg, axi_read_init_next : std_logic;    --starts read transaction
    signal axi_read_vld_s  : std_logic;    -- axi_read_data_o is valid
    signal axi_read_rdy_s  : std_logic;    -- axi_read_data_o is valid
    signal axi_read_last_s : std_logic;    -- axi_read_data_o is valid

    signal axi_base_address_reg, axi_base_address_next  : std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);  -- base address    
    signal axi_write_address_reg, axi_write_address_next : std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);  -- address added to base address
    signal axi_read_address_reg, axi_read_address_next : std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);  -- address added to base address
    signal axi_read_data_reg, axi_read_data_next : std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);  -- data read from                                                             -- ddr
    signal start_addr_reg, start_addr_next : std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
    signal clear_intr_addr_reg, clear_intr_addr_next : std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
    signal pb_status_cnt_reg, pb_status_cnt_next: std_logic_vector(1 downto 0);  
    signal setup_cnt_reg, setup_cnt_next : std_logic_vector(2 downto 0);  
    signal cnt_max_reg, cnt_max_next : std_logic_vector(1 downto 0);  

    type state_t is (IDLE, PB_STATUS_READ, PP_STATUS_READ, CTRL_READ, CTRL_SETUP, START_TASK, INC_DROP_CNT, INTR_CLEAR);
    signal state_reg, state_next : state_t;

    -- Register addresses
    constant REGS_BASE_ADDR: unsigned := x"00100000";

    constant PB_REGS_MAX: unsigned := x"3";
    constant PP_REGS_MAX: unsigned := x"4";

    constant PB0_STS: unsigned := x"04";
    constant PB0_START: unsigned := x"08";
    constant PB0_CTRL1: unsigned := x"0C";
    constant PB0_CTRL2: unsigned := x"10";
    constant PB0_CTRL3: unsigned := x"14";
    constant PB0_CTRL4: unsigned := x"18";

    constant PB1_STS: unsigned := x"1C";
    constant PB1_START: unsigned := x"20";
    constant PB1_CTRL1: unsigned := x"24";
    constant PB1_CTRL2: unsigned := x"28";
    constant PB1_CTRL3: unsigned := x"2C";
    constant PB1_CTRL4: unsigned := x"30";

    constant PP_STS: unsigned := x"34";
    constant PP_START: unsigned := x"38";
    constant PP_CTRL1: unsigned := x"3C";
    constant PP_CTRL2: unsigned := x"40";
    constant PP_CTRL3: unsigned := x"44";

    constant EX_REGS_BASE_ADDR: unsigned := x"00200000";
    constant EXT_PB_CTRL1: unsigned := x"00";
    constant EXT_PB_CTRL2: unsigned := x"04";
    constant EXT_PB_CTRL3: unsigned := x"08";
    constant EXT_PB_CTRL4: unsigned := x"0C";

    constant EXT_PP_CTRL1: unsigned := x"10";
    constant EXT_PP_CTRL2: unsigned := x"14";
    constant EXT_PP_CTRL3: unsigned := x"18";
    constant EXT_DROP_CNT: unsigned := x"1C";

begin
  -- [x] main controller implementation
  -- [x] master AXI cont added
  

  state: process(M_AXI_ACLK)
  begin
      if(M_AXI_ACLK'event and M_AXI_ACLK = '1') then
        if M_AXI_ARESETN = '1' then
          state_reg <= IDLE;

          axi_base_address_reg <= (others => '0');
          axi_write_address_reg <= (others => '0');
					axi_write_data_reg <= (others => '0');

          axi_read_address_reg <= (others => '0');
          axi_read_data_reg <= (others => '0');

          start_addr_reg <= (others => '0');
          clear_intr_addr_reg <= (others => '0');
          pb_status_cnt_reg <= (others => '0');
          setup_cnt_reg <= (others => '0');
          cnt_max_reg <= (others => '0');

          axi_write_init_reg <= '0';
          axi_read_init_reg <= '0';

          start_addr_reg <= (others => '0');
        else
          state_reg <= state_next;

          axi_base_address_reg <= axi_base_address_next ;
          axi_write_address_reg <= axi_write_address_next;
          axi_write_init_reg <= axi_write_init_next;
					axi_write_data_reg <= axi_write_data_next;

          axi_read_address_reg <= axi_read_address_next;
          axi_read_data_reg <= axi_read_data_next;

          start_addr_reg <= start_addr_next;
          clear_intr_addr_reg <= clear_intr_addr_next;
          pb_status_cnt_reg <= pb_status_cnt_next;
          setup_cnt_reg <= setup_cnt_next;
          cnt_max_reg <= cnt_max_next;
          axi_read_init_reg <= axi_read_init_next;

        end if;
      end if;
  end process; 

  -- burst len configuration
  axi_burst_len_s <= x"00";

  -- comb process
  process(state_reg, ext_irq, int_irq, axi_write_done_s, axi_read_last_s, axi_read_data_reg,
          axi_base_address_reg, axi_write_address_reg, axi_read_address_reg, start_addr_reg,
          clear_intr_addr_reg, setup_cnt_reg, cnt_max_reg, axi_read_data_next, pb_status_cnt_reg, axi_read_init_reg, axi_write_init_reg, axi_write_data_reg) is
  begin

      -- default values
      state_next <= state_reg;
      axi_base_address_next <= axi_base_address_reg;
      axi_write_address_next <= axi_write_address_reg; 
      axi_read_address_next <= axi_read_address_reg;
			-- BUG read_data is received only from axi_controller
      --axi_read_data_next  <= axi_read_data_reg;

      start_addr_next  <= start_addr_reg;
      clear_intr_addr_next <= clear_intr_addr_reg;
      setup_cnt_next <= setup_cnt_reg;
      cnt_max_next <= cnt_max_reg;
      pb_status_cnt_next <= pb_status_cnt_reg;
      
      axi_write_data_next <= axi_write_data_reg;
      axi_write_vld_s <= '0';
      axi_read_rdy_s <= '0';

      axi_read_init_next <= '0';
      axi_write_init_next <= '0';

      case state_reg is
  
          when IDLE =>
          
            axi_base_address_next <= std_logic_vector(REGS_BASE_ADDR);
					  pb_status_cnt_next <= (others => '0');
					  setup_cnt_next <= (others => '0');

            if(int_irq(0) = '1') then
              clear_intr_addr_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB0_CTRL1);
							axi_write_data_next <= x"00000001";
              axi_write_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB0_CTRL1);

							axi_write_init_next <= '1';
            	---------------------------------------- 
            	state_next <= INTR_CLEAR;
            	---------------------------------------- 
            elsif(int_irq(1) = '1') then
              clear_intr_addr_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB1_CTRL1);
							axi_write_data_next <= x"00000001";
              axi_write_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB1_CTRL1);

							axi_write_init_next <= '1';
            	---------------------------------------- 
            	state_next <= INTR_CLEAR;
            	---------------------------------------- 
            elsif(int_irq(2) = '1') then
              clear_intr_addr_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PP_CTRL1);
							axi_write_data_next <= x"00000001";
              axi_write_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PP_CTRL1);

							axi_write_init_next <= '1';
            	---------------------------------------- 
            	state_next <= INTR_CLEAR;
            	---------------------------------------- 
            else

              if(ext_irq(0) = '1') then 
                axi_base_address_next <= std_logic_vector(REGS_BASE_ADDR);
                axi_read_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB0_STS);

							  -- start transaction one cycle earlier in order to make a pulse
								-- changed only for pb task read_init
                axi_read_init_next <= '1';

                ---------------------------------------- 
                state_next <= PB_STATUS_READ;
                ---------------------------------------- 
              elsif(ext_irq(1) = '1') then
                axi_base_address_next <= std_logic_vector(REGS_BASE_ADDR);
                axi_read_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PP_STS);
							  -- start transaction one cycle earlier in order to make a pulse
								-- changed only for pb task read_init
                axi_read_init_next <= '1';

                ---------------------------------------- 
                state_next <= PP_STATUS_READ;
                ---------------------------------------- 
              else

                ---------------------------------------- 
                state_next <= IDLE;
                ---------------------------------------- 
              end if;
            end if;
  
          when PB_STATUS_READ =>

              axi_read_rdy_s <= '1';
              --axi_read_init_next <= '1';


              if(axi_read_last_s = '1') then


                clear_intr_addr_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(EXT_PB_CTRL1);


                if(axi_read_data_next(0) = '1') then
                  axi_base_address_next <= std_logic_vector(EX_REGS_BASE_ADDR);
                  axi_read_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(EXT_PB_CTRL2);
                  cnt_max_next <= std_logic_vector(to_unsigned(2, 2));
									-- start new trans one cycle earlier
								  axi_read_init_next <= '1';
									
                  
                  if(unsigned(pb_status_cnt_reg) = 0) then
                    axi_write_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB0_CTRL2);
                    start_addr_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB0_START);
                  else
                    axi_write_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB1_CTRL2);
                    start_addr_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB1_START);
                  end if;

                    ---------------------------------------- 
                    state_next <= CTRL_READ;
                    ---------------------------------------- 
                else
                  axi_base_address_next <= std_logic_vector(REGS_BASE_ADDR);
                  axi_read_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PB1_STS);
                  pb_status_cnt_next <= std_logic_vector(unsigned(pb_status_cnt_reg) + 1);

                  if(unsigned(pb_status_cnt_reg) = 1) then
                    axi_base_address_next <= std_logic_vector(EX_REGS_BASE_ADDR);
                    axi_write_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(EXT_DROP_CNT);
										-- start new trans one cycle earlier
										axi_write_init_next <= '1';
										axi_write_data_next <= x"00000001";

                    ---------------------------------------- 
                    state_next <= INC_DROP_CNT;
                    ---------------------------------------- 
                  else
										-- start new trans one cycle earlier
										axi_read_init_next <= '1';
                    ---------------------------------------- 
                    state_next <= PB_STATUS_READ;
                    ---------------------------------------- 
                    
                  end if;
                end if;
              else
                ---------------------------------------- 
                state_next <= PB_STATUS_READ;
                ---------------------------------------- 
              end if;

          when PP_STATUS_READ =>
              axi_read_rdy_s <= '1';
              -- start transaction
              -- axi_read_init_next <= '1';

              if(axi_read_last_s = '1') then

                clear_intr_addr_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(EXT_PP_CTRL1);

                if(axi_read_data_next(0) = '1') then
                  axi_base_address_next <= std_logic_vector(EX_REGS_BASE_ADDR);
                  axi_read_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(EXT_PP_CTRL2);
                  axi_write_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PP_CTRL2);
                  start_addr_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(PP_START);
                  cnt_max_next <= std_logic_vector(to_unsigned(1, 2));
									-- start new trans one cycle earlier
									axi_read_init_next <= '1';

                  ---------------------------------------- 
                  state_next <= CTRL_READ;
                  ---------------------------------------- 
                else
                  axi_base_address_next <= std_logic_vector(EX_REGS_BASE_ADDR);
                  axi_read_address_next <= std_logic_vector(to_unsigned(0, C_M_AXI_DATA_WIDTH-8))&std_logic_vector(EXT_DROP_CNT);
									-- start new trans one cycle earlier
									axi_write_init_next <= '1';
									axi_write_data_next <= x"00000001";

                  ---------------------------------------- 
                  state_next <= INC_DROP_CNT;
                  ---------------------------------------- 
                end if;
              else

                ---------------------------------------- 
                state_next <= PP_STATUS_READ;
                ---------------------------------------- 
              end if;

          
          when CTRL_READ =>
              axi_read_rdy_s <= '1';
              --  axi_read_init_next <= '1';

              if(axi_read_last_s = '1') then
                axi_base_address_next <= std_logic_vector(REGS_BASE_ADDR);

								-- start new trans one cycle earlier
								axi_write_init_next <= '1';

								-- register read data to write_reg
								axi_write_data_next <= axi_read_data_next;

                ---------------------------------------- 
                state_next <= CTRL_SETUP;
                ---------------------------------------- 
              else
                ---------------------------------------- 
                state_next <= CTRL_READ;
                ---------------------------------------- 
              end if;

          when CTRL_SETUP =>
              -- axi_write_data_s <= axi_read_data_reg;
							-- data is valid because write_data is ready in write_data_reg
              axi_write_vld_s <= '1';

              if(axi_write_done_s = '1') then 
                setup_cnt_next <= std_logic_vector(unsigned(setup_cnt_reg) + 1);
                if(unsigned(setup_cnt_reg) = unsigned(cnt_max_reg)) then
                  axi_write_address_next <= start_addr_reg;

									-- start new trans one cycle earlier
									axi_write_init_next <= '1';
									axi_write_data_next <= x"00000001";
                  ---------------------------------------- 
                  state_next <= START_TASK;
                  ---------------------------------------- 
                else 
                  -- Read new ctrl register
                  axi_base_address_next <= std_logic_vector(EX_REGS_BASE_ADDR);
                  axi_read_address_next <= std_logic_vector(unsigned(axi_read_address_reg) + 4);
                  axi_write_address_next <= std_logic_vector(unsigned(axi_write_address_reg) + 4);

									-- start new trans one cycle earlier
									axi_read_init_next <= '1';
                  ---------------------------------------- 
                  state_next <= CTRL_READ;
                  ---------------------------------------- 
                end if;

              else
                ---------------------------------------- 
                state_next <= CTRL_SETUP;
                ---------------------------------------- 
              end if;
          when START_TASK =>
              -- axi_write_data_s(0) <= '1';
              axi_write_vld_s <= '1';

              if(axi_write_done_s = '1') then
                axi_base_address_next <= std_logic_vector(REGS_BASE_ADDR);
                axi_write_address_next <= clear_intr_addr_reg;
                
								-- start new trans one cycle earlier
								axi_write_init_next <= '1';
								-- write data takes previous value
                ---------------------------------------- 
                state_next <= INTR_CLEAR;
                ---------------------------------------- 
              else
                ---------------------------------------- 
                state_next <= START_TASK;
                ---------------------------------------- 
              end if;
          when INC_DROP_CNT =>
              -- axi_write_data_s(0) <= '1';
              axi_write_vld_s <= '1';

              if(axi_write_done_s = '1') then
                axi_base_address_next <= std_logic_vector(EX_REGS_BASE_ADDR);
                axi_write_address_next <= clear_intr_addr_reg;
                
								-- start new trans one cycle earlier
								axi_write_init_next <= '1';
                ---------------------------------------- 
                state_next <= INTR_CLEAR;
                ---------------------------------------- 
              else
                ---------------------------------------- 
                state_next <= INC_DROP_CNT;
                ---------------------------------------- 
              end if;
          when INTR_CLEAR =>
              -- axi_write_data_s(0) <= '1';
              axi_write_vld_s <= '1';

              if(axi_write_done_s = '1') then
                ---------------------------------------- 
                state_next <= IDLE;
                ---------------------------------------- 
              else
                ---------------------------------------- 
                state_next <= INTR_CLEAR;
                ---------------------------------------- 
              end if;
  
      end case;
  end process;
  

  master_axi_cont_ctrl: master_axi_cont
  generic map(
      C_M_AXI_ADDR_WIDTH => C_M_AXI_ADDR_WIDTH,
      C_M_AXI_DATA_WIDTH => C_M_AXI_DATA_WIDTH
  )
  port map(
    -- [x] Connect with actual controller signals

    AXI_BURST_LEN  => axi_burst_len_s, 

    AXI_BASE_ADDRESS_I  => axi_base_address_reg, 
    AXI_WRITE_ADDRESS_I => axi_write_address_reg, 
    AXI_WRITE_INIT_I    => axi_write_init_reg, 
    AXI_WRITE_DATA_I    => axi_write_data_reg, 
    AXI_WRITE_VLD_I     => axi_write_vld_s, 
    AXI_WRITE_STRB_I     => (others => '1'), 
    AXI_WRITE_RDY_O     => axi_write_rdy_s, 
    AXI_WRITE_DONE_O    => axi_write_done_s, 
    AXI_READ_ADDRESS_I => axi_read_address_reg, 
    AXI_READ_INIT_I => axi_read_init_reg, 
    AXI_READ_DATA_O => axi_read_data_next, 
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
