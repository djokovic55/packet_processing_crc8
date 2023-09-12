
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;
-- use work.utils_pkg.all;

entity slave_axi_lite_regs_cont is
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
  -- IMPORTANT can be connected as rlast?
  S_AXI_RVALID : out std_logic;
  S_AXI_RREADY : in std_logic);
end slave_axi_lite_regs_cont;

architecture arch_imp of slave_axi_lite_regs_cont is
 -- AXI4LITE signals
  signal axi_awaddr : std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
  signal axi_awready : std_logic;
  signal axi_wready : std_logic;
  signal axi_bresp : std_logic_vector(1 downto 0);
  signal axi_bvalid : std_logic;
  signal axi_araddr : std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
  signal axi_arready : std_logic;
  signal axi_rdata : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
  signal axi_rresp : std_logic_vector(1 downto 0);
  signal axi_rvalid : std_logic;
  -- Example-specific design signals
  -- local parameter for addressing 32 bit / 64 bit C_S_AXI_DATA_WIDTH
  -- ADDR_LSB is used for addressing 32/64 bit registers/memories
  -- ADDR_LSB = 2 for 32 bits (n downto 2)
  -- ADDR_LSB = 3 for 64 bits (n downto 3)
  constant ADDR_LSB : integer := (C_S_AXI_DATA_WIDTH/32)+ 1;
  -- for 17 regs
  constant OPT_MEM_ADDR_BITS : integer := 4;
  ------------------------------------------------
  ---- Signals for user logic register space example
  --------------------------------------------------
  ---- Number of Slave Registers 5
  signal slv_reg_rden : std_logic;
  signal slv_reg_wren : std_logic;
  signal reg_data_out : std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
  signal byte_index : integer;
  begin
  -- I/O Connections assignments
  S_AXI_AWREADY<= axi_awready;
  S_AXI_WREADY <= axi_wready;
  S_AXI_BRESP <= axi_bresp;
  S_AXI_BVALID <= axi_bvalid;
  S_AXI_ARREADY <= axi_arready;
  S_AXI_RDATA <= axi_rdata;
  S_AXI_RRESP <= axi_rresp;
  S_AXI_RVALID <= axi_rvalid;
  
  -- Implement axi_awready generation
  -- axi_awready is asserted for one S_AXI_ACLK clock cycle when both S_AXI_AWVALID and
  -- S_AXI_WVALID are asserted. axi_awready is de-asserted when reset is low. 
  process (S_AXI_ACLK)
  begin
    if rising_edge(S_AXI_ACLK) then
      if S_AXI_ARESETN = '1' then
        axi_awready <= '0';
        else
            if (axi_awready = '0' and S_AXI_AWVALID = '1' and S_AXI_WVALID = '1') then
            -- Slave is ready to accept write address when there is a valid write address
            -- and write data on the write address and data bus. This design expects no outstanding transactions.
            axi_awready <= '1';
          else
            axi_awready <= '0';
          end if;
      end if;
    end if;
  end process;

  -- Implement axi_awaddr latching
  -- This process is used to latch the address when both S_AXI_AWVALID and S_AXI_WVALID are valid.
  process (S_AXI_ACLK)
  begin
    if rising_edge(S_AXI_ACLK) then
      if S_AXI_ARESETN = '1' then
        axi_awaddr <= (others => '0');
      else
        if (axi_awready = '0' and S_AXI_AWVALID = '1' and S_AXI_WVALID = '1') then
          -- Write Address latching
          axi_awaddr <= S_AXI_AWADDR;
        end if;
      end if;
    end if; 
  end process; 

  -- Implement axi_wready generation
  -- axi_wready is asserted for one S_AXI_ACLK clock cycle when both S_AXI_AWVALID and
  -- S_AXI_WVALID are asserted. axi_wready is de-asserted when reset is low.
  process (S_AXI_ACLK)
  begin
    if rising_edge(S_AXI_ACLK) then
      if S_AXI_ARESETN = '1' then
        axi_wready <= '0';
        else
        if (axi_wready = '0' and S_AXI_WVALID = '1' and S_AXI_AWVALID = '1') then
            -- Slave is ready to accept write data when there is a valid write address and
            -- write data on the write address and data bus. This design expects no outstanding transactions.
            axi_wready <= '1';
          else
            axi_wready <= '0';
        end if;
      end if;
    end if;
  end process; 

  -- IMPORTANT Implement memory mapped register select and write logic generation
  -- The write data is accepted and written to memory mapped registers when axi_awready, S_AXI_WVALID,
  -- axi_wready and S_AXI_WVALID are asserted. Write strobes are used to select byte enables of slave
  -- registers while writing. These registers are cleared when reset (active low) is applied. Slave register write
  -- enable is asserted when valid address and data are available and the slave is ready to accept the write 
  -- address and write data.
  slv_reg_wren <= axi_wready and S_AXI_WVALID and axi_awready and S_AXI_AWVALID;
  process (S_AXI_ACLK)
    variable loc_addr : std_logic_vector(OPT_MEM_ADDR_BITS downto 0); 
  begin
    if rising_edge(S_AXI_ACLK) then
      if S_AXI_ARESETN = '1' then


        sys_cfg_wr_o <= '0';

        pb0_ctrl0_wr_o <= '0';
        pb0_ctrl1_wr_o <= '0';
        pb0_ctrl2_wr_o <= (others => '0');
        pb0_ctrl3_wr_o <= (others => '0');
        pb0_ctrl4_wr_o <= (others => '0');

        pb1_ctrl0_wr_o <= '0';
        pb1_ctrl1_wr_o <= '0';
        pb1_ctrl2_wr_o <= (others => '0');
        pb1_ctrl3_wr_o <= (others => '0');
        pb1_ctrl4_wr_o <= (others => '0');
        
        pp_ctrl0_wr_o <= '0';
        pp_ctrl1_wr_o <= '0';
        pp_ctrl2_wr_o <= (others => '0');
        pp_ctrl3_wr_o <= '0';

      else
        -- Default assignments
        
        sys_cfg_wr_o <= '0';
        pb0_ctrl0_wr_o <= '0';
        pb0_ctrl1_wr_o <= '0';
        pb0_ctrl2_wr_o <= (others => '0');
        pb0_ctrl3_wr_o <= (others => '0');
        pb0_ctrl4_wr_o <= (others => '0');

        pb1_ctrl0_wr_o <= '0';
        pb1_ctrl1_wr_o <= '0';
        pb1_ctrl2_wr_o <= (others => '0');
        pb1_ctrl3_wr_o <= (others => '0');
        pb1_ctrl4_wr_o <= (others => '0');
        
        pp_ctrl0_wr_o <= '0';
        pp_ctrl1_wr_o <= '0';
        pp_ctrl2_wr_o <= (others => '0');
        pp_ctrl3_wr_o <= '0';

        loc_addr := axi_awaddr(ADDR_LSB + OPT_MEM_ADDR_BITS downto ADDR_LSB);
        if (slv_reg_wren = '1') then
          case loc_addr is
          when "00000" =>
            sys_cfg_wr_o <= '1';
          --when x"01" => RO reg

          when "00010" =>
            pb0_ctrl0_wr_o <= '1';
          when "00011" =>
            pb0_ctrl1_wr_o <= '1';
          when "00100" =>
            pb0_ctrl2_wr_o <= S_AXI_WSTRB;
          when "00101" =>
            pb0_ctrl3_wr_o <= S_AXI_WSTRB;
          when "00110" =>
            pb0_ctrl4_wr_o <= S_AXI_WSTRB;
          --when x"07" => RO reg
          
          when "01000" =>
            pb1_ctrl0_wr_o <= '1';
          when "01001" =>
            pb1_ctrl1_wr_o <= '1';
          when "01010" =>
            pb1_ctrl2_wr_o <= S_AXI_WSTRB;
          when "01011" =>
            pb1_ctrl3_wr_o <= S_AXI_WSTRB;
          when "01100" =>
            pb1_ctrl4_wr_o <= S_AXI_WSTRB;
          --when x"0d" => RO reg

          when "01110" =>
            pp_ctrl0_wr_o <= '1';
          when "01111" =>
            pp_ctrl1_wr_o <= '1';
          when "10000" =>
            pp_ctrl2_wr_o <= S_AXI_WSTRB;
          when "10001" =>
            pp_ctrl3_wr_o <= '1';
          when others =>
          end case;
        end if;
      end if;
    end if; 
  end process; 

  -- Implement write response logic generation
  -- The write response and response valid signals are asserted by the slave when
  -- axi_wready, S_AXI_WVALID, axi_wready and S_AXI_WVALID are asserted. 
  -- This marks the acceptance of address and indicates the status of write transaction.
  process (S_AXI_ACLK)
  begin
    if rising_edge(S_AXI_ACLK) then
      if S_AXI_ARESETN = '1' then
        axi_bvalid <= '0';
        axi_bresp <= "00"; --need to work more on the responses
      else
        if (axi_awready = '1' and S_AXI_AWVALID = '1' and axi_wready = '1' 
        and S_AXI_WVALID = '1' and axi_bvalid = '0' ) then
          axi_bvalid <= '1';
          axi_bresp <= "00"; 
        elsif (S_AXI_BREADY = '1' and axi_bvalid = '1') then 
          --check if bready is asserted while bvalid is high)
          axi_bvalid <= '0'; -- (there is a possibility that bready is always asserted high)
        end if;
      end if;
    end if; 
  end process; 

  -- Implement axi_arready generation
  -- axi_arready is asserted for one S_AXI_ACLK clock cycle when S_AXI_ARVALID 
  -- is asserted. axi_awready is de-asserted when reset (active low) is asserted. 
  -- The read address is also latched when S_AXI_ARVALID is asserted.
  -- axi_araddr is reset to zero on reset assertion.
  process (S_AXI_ACLK)
  begin
    if rising_edge(S_AXI_ACLK) then
      if S_AXI_ARESETN = '1' then
        axi_arready <= '0';
        axi_araddr <= (others => '1');
      else
        if (axi_arready = '0' and S_AXI_ARVALID = '1') then
          -- indicates that the slave has acceped the valid read address
          axi_arready <= '1';
          -- Read Address latching 
          axi_araddr <= S_AXI_ARADDR; 
        else
          axi_arready <= '0';
        end if;
      end if;
    end if; 
  end process; 

  -- Implement axi_arvalid generation
  -- axi_rvalid is asserted for one S_AXI_ACLK clock cycle when both 
  -- S_AXI_ARVALID and axi_arready are asserted. The slave registers data are
  -- available on the axi_rdata bus at this instance. The assertion of axi_rvalid marks
  -- the validity of read data on the bus and axi_rresp indicates the status of read
  -- transaction. axi_rvalid is deasserted on reset (active low).
  -- axi_rresp and axi_rdata are cleared to zero on reset (active low). 
  process (S_AXI_ACLK)
  begin
  if rising_edge(S_AXI_ACLK) then
    if S_AXI_ARESETN = '1' then
      axi_rvalid <= '0';
      axi_rresp <= "00";
    else
      if (axi_arready = '1' and S_AXI_ARVALID = '1' and axi_rvalid = '0') then
        -- Valid read data is available at the read data bus
        axi_rvalid <= '1';
        axi_rresp <= "00"; -- 'OKAY' response
      elsif (axi_rvalid = '1' and S_AXI_RREADY = '1') then
        -- Read data is accepted by the master
        axi_rvalid <= '0';
      end if; 
    end if;
  end if;
  end process;

  -- Implement memory mapped register select and read logic generation
  -- Slave register read enable is asserted when valid address is available
  -- and the slave is ready to accept the read address.
  slv_reg_rden <= axi_arready and S_AXI_ARVALID and (not axi_rvalid) ;

  process (sys_cfg_i, pb0_sts_i, pb1_sts_i, pp_sts_i, 
           pb0_ctrl0_i, pb0_ctrl1_i, pb0_ctrl2_i, pb0_ctrl3_i, pb0_ctrl4_i, 
           pb1_ctrl0_i, pb1_ctrl1_i, pb1_ctrl2_i, pb1_ctrl3_i, pb1_ctrl4_i, 
           pp_ctrl0_i, pp_ctrl1_i, pp_ctrl2_i, pp_ctrl3_i)

  variable loc_addr :std_logic_vector(OPT_MEM_ADDR_BITS downto 0);
  begin
    -- Address decoding for reading registers
    loc_addr := axi_araddr(ADDR_LSB + OPT_MEM_ADDR_BITS downto ADDR_LSB);
    case loc_addr is
    when "00000" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-3))&sys_cfg_i;
    when "00001" => 
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pb0_sts_i;
    when "00010" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pb0_ctrl0_i;
    when "00011" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pb0_ctrl1_i;
    when "00100" =>
      reg_data_out <= pb0_ctrl2_i;
    when "00101" =>
      reg_data_out <= pb0_ctrl3_i;
    when "00110" =>
      reg_data_out <= pb0_ctrl4_i;

    when "00111" => 
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pb1_sts_i;
    when "01000" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pb1_ctrl0_i;
    when "01001" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pb1_ctrl1_i;
    when "01010" =>
      reg_data_out <= pb1_ctrl2_i;
    when "01011" =>
      reg_data_out <= pb1_ctrl3_i;
    when "01100" =>
      reg_data_out <= pb1_ctrl4_i;

    when "01101" => 
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-12))&pp_sts_i;
    when "01110" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pp_ctrl0_i;
    when "01111" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pp_ctrl1_i;
    when "10000" =>
      reg_data_out <= pp_ctrl2_i;
    when "10001" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&pp_ctrl3_i;
    when others =>
    end case;
  end process; 

  -- Output register or memory read data
  process( S_AXI_ACLK) is
  begin
    if (rising_edge (S_AXI_ACLK)) then
      if ( S_AXI_ARESETN = '1' ) then
        axi_rdata <= (others => '0');
      else
        if (slv_reg_rden = '1') then
          -- When there is a valid read address (S_AXI_ARVALID) with acceptance of
          -- read address by the slave (axi_arready), output the read data
          -- Read address mux
          axi_rdata <= reg_data_out; -- register read data
        end if; 
      end if;
    end if;
  end process;

  -- Add user logic here
  process (S_AXI_ACLK)
  begin
    if (S_AXI_ACLK'event and S_AXI_ACLK = '1') then
      reg_data_o <= S_AXI_WDATA;
    end if;
  end process;
 -- User logic ends
 
end arch_imp;
