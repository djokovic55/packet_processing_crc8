library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- use work.utils_pkg.all;

entity slave_axi_lite_ex_regs_cont is
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
	ext_pb_ctrl2_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0); -- in_addr
	ext_pb_ctrl3_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
	ext_pb_ctrl4_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);

	ext_pp_ctrl1_i : in std_logic;
	ext_pp_ctrl2_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
	ext_pp_ctrl3_i : in std_logic;

	ext_drop_cnt_i : in std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
  -- User ports ends
  -- Do not modify the ports beyond this line
  S_AXI_ACLK : in std_logic;
  S_AXI_ARESETN : in std_logic;

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
end slave_axi_lite_ex_regs_cont;
architecture arch_imp of slave_axi_lite_ex_regs_cont is
 -- AXI4LITE signals
	signal axi_awaddr	: std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
	signal axi_awready	: std_logic;
	signal axi_wready	: std_logic;
	signal axi_bresp	: std_logic_vector(1 downto 0);
	-- signal axi_buser	: std_logic_vector(C_S_AXI_BUSER_WIDTH-1 downto 0);
	signal axi_bvalid	: std_logic;
	signal axi_araddr	: std_logic_vector(C_S_AXI_ADDR_WIDTH-1 downto 0);
	signal axi_arready	: std_logic;
	signal axi_rdata	: std_logic_vector(C_S_AXI_DATA_WIDTH-1 downto 0);
	signal axi_rresp	: std_logic_vector(1 downto 0);
	signal axi_rlast	: std_logic;
	-- signal axi_ruser	: std_logic_vector(C_S_AXI_RUSER_WIDTH-1 downto 0);
	signal axi_rvalid	: std_logic;

  -- NEW
	signal  aw_wrap_en : std_logic; 
	-- ar_wrap_en determines wrap boundary and enables wrapping
	signal  ar_wrap_en : std_logic;
	-- aw_wrap_size is the size of the write transfer, the
	-- write address wraps to a lower address if upper address
	-- limit is reached
	signal aw_wrap_size : integer;
	-- ar_wrap_size is the size of the read transfer, the
	-- read address wraps to a lower address if upper address
	-- limit is reached
	signal ar_wrap_size : integer;
	-- The axi_awv_awr_flag flag marks the presence of write address valid
	signal axi_awv_awr_flag    : std_logic;
	--The axi_arv_arr_flag flag marks the presence of read address valid
	signal axi_arv_arr_flag    : std_logic;
	-- The axi_awlen_cntr internal write address counter to keep track of beats in a burst transaction
	signal axi_awlen_cntr      : std_logic_vector(7 downto 0);
	--The axi_arlen_cntr internal read address counter to keep track of beats in a burst transaction
	signal axi_arlen_cntr      : std_logic_vector(7 downto 0);
	signal axi_arburst      : std_logic_vector(2-1 downto 0);
	signal axi_awburst      : std_logic_vector(2-1 downto 0);
	signal axi_arlen      : std_logic_vector(8-1 downto 0);
	signal axi_awlen      : std_logic_vector(8-1 downto 0);
  -- new
  -- Example-specific design signals
  -- local parameter for addressing 32 bit / 64 bit C_S_AXI_DATA_WIDTH
  -- ADDR_LSB is used for addressing 32/64 bit registers/memories
  -- ADDR_LSB = 2 for 32 bits (n downto 2)
  -- ADDR_LSB = 3 for 64 bits (n downto 3)
  constant ADDR_LSB : integer := (C_S_AXI_DATA_WIDTH/32)+ 1;
  constant OPT_MEM_ADDR_BITS : integer := 2;
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
	S_AXI_AWREADY	<= axi_awready;
	S_AXI_WREADY	<= axi_wready;
	S_AXI_BRESP	<= axi_bresp;
	S_AXI_BVALID	<= axi_bvalid;
	S_AXI_ARREADY	<= axi_arready;
	S_AXI_RDATA	<= axi_rdata;
	S_AXI_RRESP	<= axi_rresp;
	S_AXI_RLAST	<= axi_rlast;
	S_AXI_RVALID	<= axi_rvalid;

  -- Implement axi_awready generation
  -- axi_awready is asserted for one S_AXI_ACLK clock cycle when both S_AXI_AWVALID and
  -- S_AXI_WVALID are asserted. axi_awready is de-asserted when reset is low. 

	process (S_AXI_ACLK)
	begin
	  if rising_edge(S_AXI_ACLK) then 
	    if S_AXI_ARESETN = '1' then
	      axi_awready <= '0';
	      axi_awv_awr_flag <= '0';
	    else
	      if (axi_awready = '0' and S_AXI_AWVALID = '1' and axi_awv_awr_flag = '0' and axi_arv_arr_flag = '0') then
	        -- slave is ready to accept an address and
	        -- associated control signals
	        axi_awv_awr_flag  <= '1'; -- used for generation of bresp() and bvalid
	        axi_awready <= '1';
	      elsif (S_AXI_WLAST = '1' and axi_wready = '1') then 
	      -- preparing to accept next address after current write burst tx completion
	        axi_awv_awr_flag  <= '0';
				-- single burst transaction
	      elsif (unsigned(S_AXI_AWLEN) = 0 and axi_wready = '1') then 
	        axi_awv_awr_flag  <= '0';
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
	      axi_awburst <= (others => '0'); 
	      axi_awlen <= (others => '0'); 
	      axi_awlen_cntr <= (others => '0');
	    else
	      if (axi_awready = '0' and S_AXI_AWVALID = '1' and axi_awv_awr_flag = '0') then
	      -- address latching 
	        axi_awaddr <= S_AXI_AWADDR(C_S_AXI_ADDR_WIDTH - 1 downto 0);  ---- start address of transfer
	        axi_awlen_cntr <= (others => '0');
	        axi_awburst <= S_AXI_AWBURST;
	        axi_awlen <= S_AXI_AWLEN;
	      elsif((axi_awlen_cntr <= axi_awlen) and axi_wready = '1' and S_AXI_WVALID = '1') then     
	        axi_awlen_cntr <= std_logic_vector (unsigned(axi_awlen_cntr) + 1);

	        case (axi_awburst) is
	          when "00" => -- fixed burst
	            -- The write address for all the beats in the transaction are fixed
	            axi_awaddr     <= axi_awaddr;       ----for awsize = 4 bytes (010)
	          when "01" => --incremental burst
	            -- The write address for all the beats in the transaction are increments by awsize
	            axi_awaddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB) <= std_logic_vector (unsigned(axi_awaddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB)) + 1);--awaddr aligned to 4 byte boundary
	            axi_awaddr(ADDR_LSB-1 downto 0)  <= (others => '0');  ----for awsize = 4 bytes (010)
	          when "10" => --Wrapping burst
	            -- The write address wraps when the address reaches wrap boundary 
	            if (aw_wrap_en = '1') then
	              axi_awaddr <= std_logic_vector (unsigned(axi_awaddr) - (to_unsigned(aw_wrap_size,C_S_AXI_ADDR_WIDTH)));                
	            else 
	              axi_awaddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB) <= std_logic_vector (unsigned(axi_awaddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB)) + 1);--awaddr aligned to 4 byte boundary
	              axi_awaddr(ADDR_LSB-1 downto 0)  <= (others => '0');  ----for awsize = 4 bytes (010)
	            end if;
	          when others => --reserved (incremental burst for example)
	            axi_awaddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB) <= std_logic_vector (unsigned(axi_awaddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB)) + 1);--for awsize = 4 bytes (010)
	            axi_awaddr(ADDR_LSB-1 downto 0)  <= (others => '0');
	        end case;        
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
	      if (axi_wready = '0' and S_AXI_WVALID = '1' and axi_awv_awr_flag = '1') then
	        axi_wready <= '1';
	        -- elsif (axi_awv_awr_flag = '0') then
	      elsif (S_AXI_WLAST = '1' and axi_wready = '1') then 
	        axi_wready <= '0';
	      elsif (unsigned(S_AXI_AWLEN) = 0 and axi_wready = '1') then 
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
  slv_reg_wren <= axi_wready and S_AXI_WVALID;
  process (S_AXI_WSTRB, axi_awaddr)
    variable loc_addr : std_logic_vector(OPT_MEM_ADDR_BITS downto 0); 
  begin
      -- Default assignments
      ext_pb_ctrl1_wr_o <= '0';
      ext_pp_ctrl1_wr_o <= '0';
      ext_drop_cnt_wr_o <= '0';
      
      loc_addr := axi_awaddr(ADDR_LSB + OPT_MEM_ADDR_BITS downto ADDR_LSB);
      if (slv_reg_wren = '1') then
        case loc_addr is
        when b"000" =>
          ext_pb_ctrl1_wr_o <= '1';
        when b"100" =>
          ext_pp_ctrl1_wr_o <= '1';
        when b"111" =>
          ext_drop_cnt_wr_o <= '1';
        when others =>
        end case;
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
	      axi_bvalid  <= '0';
	      axi_bresp  <= "00"; --need to work more on the responses
	      -- axi_buser <= (others => '0');
	    else
	      if (axi_awv_awr_flag = '1' and axi_wready = '1' and S_AXI_WVALID = '1' and axi_bvalid = '0' and (S_AXI_WLAST = '1' or unsigned(S_AXI_AWLEN) = 0)) then
	        axi_bvalid <= '1';
	        axi_bresp  <= "00"; 
	      elsif (S_AXI_BREADY = '1' and axi_bvalid = '1') then  
	      --check if bready is asserted while bvalid is high)
	        axi_bvalid <= '0';                      
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
	      axi_arv_arr_flag <= '0';
	    else
	      if (axi_arready = '0' and S_AXI_ARVALID = '1' and axi_awv_awr_flag = '0' and axi_arv_arr_flag = '0') then
	        axi_arready <= '1';
	        axi_arv_arr_flag <= '1';
	      elsif (axi_rvalid = '1' and S_AXI_RREADY = '1' and (axi_arlen_cntr = axi_arlen)) then 
	      -- preparing to accept next address after current read completion
	        axi_arv_arr_flag <= '0';
	      else
	        axi_arready <= '0';
	      end if;
	    end if;
	  end if;         
	end process; 

	-- Implement axi_araddr latching
	--This process is used to latch the address when both 
	--S_AXI_ARVALID and S_AXI_RVALID are valid. 
	process (S_AXI_ACLK)
	begin
	  if rising_edge(S_AXI_ACLK) then 
	    if S_AXI_ARESETN = '1' then
	      axi_arburst <= (others => '0');
	      axi_arlen <= (others => '0'); 
	      axi_rlast <= '0';
	      -- axi_ruser <= (others => '0');
	    else
	      if (axi_arready = '0' and S_AXI_ARVALID = '1' and axi_arv_arr_flag = '0') then
	        axi_rlast <= '0';
	        axi_arburst <= S_AXI_ARBURST;
	        axi_arlen <= S_AXI_ARLEN;

				elsif((unsigned(axi_arlen_cntr) = unsigned(axi_arlen) - 1) and axi_rlast = '0' and axi_arv_arr_flag = '1' and axi_rvalid = '1' and S_AXI_RREADY = '1') then  
	        axi_rlast <= '1';
				-- rlast will remain asserted until rready
	      elsif (axi_rlast = '1' and S_AXI_RREADY = '1') then  
	        axi_rlast <= '0';
	      elsif (unsigned(axi_arlen) = 0) then  
	        axi_rlast <= '0';
	      end if;
	    end if;
	  end if;
	end  process;  

	-- burst length counter
	process (S_AXI_ACLK)
	begin
	  if rising_edge(S_AXI_ACLK) then 
	    if S_AXI_ARESETN = '1' then
				axi_arlen_cntr <= (others => '0');
				axi_araddr <= (others => '0');
			else

				if(axi_arready = '0' and S_AXI_ARVALID = '1' and axi_arv_arr_flag = '0') then
					axi_arlen_cntr <= (others => '0');
	        axi_araddr <= S_AXI_ARADDR(C_S_AXI_ADDR_WIDTH - 1 downto 0); ---- start address of transfer
				elsif(axi_rvalid = '1' and S_AXI_RREADY = '1' and unsigned(axi_arlen_cntr) < unsigned(axi_arlen)) then
					axi_arlen_cntr <= std_logic_vector(unsigned(axi_arlen_cntr) + 1);
					case (axi_arburst) is
						when "00" =>  -- fixed burst
								-- The read address for all the beats in the transaction are fixed
								axi_araddr     <= axi_araddr;      ----for arsize = 4 bytes (010)
						when "01" =>  --incremental burst
								-- The read address for all the beats in the transaction are increments by awsize
								axi_araddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB) <= std_logic_vector (unsigned(axi_araddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB)) + 1); --araddr aligned to 4 byte boundary
								axi_araddr(ADDR_LSB-1 downto 0)  <= (others => '0');  ----for awsize = 4 bytes (010)
						when "10" =>  --Wrapping burst
								-- The read address wraps when the address reaches wrap boundary 
								if (ar_wrap_en = '1') then   
										axi_araddr <= std_logic_vector (unsigned(axi_araddr) - (to_unsigned(ar_wrap_size,C_S_AXI_ADDR_WIDTH)));
								else 
										axi_araddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB) <= std_logic_vector (unsigned(axi_araddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB)) + 1); --araddr aligned to 4 byte boundary
										axi_araddr(ADDR_LSB-1 downto 0)  <= (others => '0');  ----for awsize = 4 bytes (010)
								end if;
						when others => --reserved (incremental burst for example)
								axi_araddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB) <= std_logic_vector (unsigned(axi_araddr(C_S_AXI_ADDR_WIDTH - 1 downto ADDR_LSB)) + 1);--for arsize = 4 bytes (010)
							axi_araddr(ADDR_LSB-1 downto 0)  <= (others => '0');
					end case;         
				end if;
			end if;
		end if;
	end process;
			
	-- Implement axi_arvalid generation

	-- axi_rvalid is asserted for one S_AXI_ACLK clock cycle when both 
	-- S_AXI_ARVALID and axi_arready are asserted. The slave registers 
	-- data are available on the axi_rdata bus at this instance. The 
	-- assertion of axi_rvalid marks the validity of read data on the 
	-- bus and axi_rresp indicates the status of read transaction.axi_rvalid 
	-- is deasserted on reset (active low). axi_rresp and axi_rdata are 
	-- cleared to zer/o on reset (active low).  

	process (S_AXI_ACLK)
	begin
	  if rising_edge(S_AXI_ACLK) then
	    if S_AXI_ARESETN = '1' then
	      axi_rvalid <= '0';
	      axi_rresp  <= "00";
	    else
	      if (axi_arv_arr_flag = '1' and axi_rvalid = '0') then
	        axi_rvalid <= '1';
	        axi_rresp  <= "00"; -- 'OKAY' response
	      elsif (axi_rvalid = '1' and S_AXI_RREADY = '1' and (unsigned(axi_arlen_cntr) = unsigned(axi_arlen))) then
	        axi_rvalid <= '0';
	      end  if;      
	    end if;
	  end if;
	end  process;
  -- Implement memory mapped register select and read logic generation
  -- Slave register read enable is asserted when valid address is available
  -- and the slave is ready to accept the read address.
  slv_reg_rden <= axi_rvalid;

  process (ext_pb_ctrl1_i, ext_pb_ctrl2_i, ext_pb_ctrl3_i, ext_pb_ctrl4_i, 
  ext_pp_ctrl1_i, ext_pp_ctrl2_i, ext_pp_ctrl3_i, ext_drop_cnt_i, 
  axi_araddr, S_AXI_ARESETN, slv_reg_rden)

  variable loc_addr :std_logic_vector(OPT_MEM_ADDR_BITS downto 0);
  begin
    -- Address decoding for reading registers
    loc_addr := axi_araddr(ADDR_LSB + OPT_MEM_ADDR_BITS downto ADDR_LSB);
    case loc_addr is
    when b"000" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&ext_pb_ctrl1_i;
    when b"001" =>
      reg_data_out <= ext_pb_ctrl2_i;
    when b"010" =>
      reg_data_out <= ext_pb_ctrl3_i;
    when b"011" =>
      reg_data_out <= ext_pb_ctrl4_i;
    when b"100" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&ext_pp_ctrl1_i;
    when b"101" =>
      reg_data_out <= ext_pp_ctrl2_i;
    when b"110" =>
      reg_data_out <= std_logic_vector(to_unsigned(0, C_S_AXI_DATA_WIDTH-1))&ext_pp_ctrl3_i;
    when b"111" =>
      reg_data_out <= ext_drop_cnt_i;
    when others =>
      reg_data_out <= (others => '0');
    end case;
  end process; 

	axi_rdata <= reg_data_out when slv_reg_rden = '1' else (others => '0');

  -- -- Output register or memory read data
  -- process( S_AXI_ACLK) is
  -- begin
  --   if (rising_edge (S_AXI_ACLK)) then
  --     if ( S_AXI_ARESETN = '1' ) then
  --       axi_rdata <= (others => '0');
  --     else
  --       if (slv_reg_rden = '1') then
  --         -- When there is a valid read address (S_AXI_ARVALID) with acceptance of
  --         -- read address by the slave (axi_arready), output the read data
  --         -- Read address mux
  --         axi_rdata <= reg_data_out; -- register read data
  --       end if; 
  --     end if;
  --   end if;
  -- end process;

  reg_data_o <= S_AXI_WDATA;
  -- -- Add user logic here
  -- process (S_AXI_ACLK)
  -- begin
  --   if (S_AXI_ACLK'event and S_AXI_ACLK = '1') then
  --     reg_data_o <= S_AXI_WDATA;
  --   end if;
  -- end process;
 -- User logic ends
 
end arch_imp;
