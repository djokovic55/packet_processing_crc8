
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- testing git option
entity master_axi_cont is
	generic (
		-- Users to add parameters here

		-- User parameters ends
		-- Do not modify the parameters beyond this line

		-- Base address of targeted slave
		-- C_M_TARGET_SLAVE_BASE_ADDR	: std_logic_vector	:= x"00000000";
		-- // FIXME Burst length must be configurable
		-- Burst Length. Supports 1, 2, 4, 8, 16, 32, 64, 128, 256 burst lengths
		C_M_AXI_BURST_LEN	: integer	:= 16;
		-- Width of Address Bus
		C_M_AXI_ADDR_WIDTH	: integer	:= 32;
		-- Width of Data Bus
		C_M_AXI_DATA_WIDTH	: integer	:= 32
	);
	port (
		-- Users to add ports here

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
end master_axi_cont;

architecture implementation of master_axi_cont is


	-- function called clogb2 that returns an integer which has the
	--value of the ceiling of the log base 2

	function clogb2 (bit_depth : integer) return integer is            
	 	variable depth  : integer := bit_depth;                               
	 	variable count  : integer := 1;                                       
	 begin                                                                   
	 	 for clogb2 in 1 to bit_depth loop  -- Works for up to 32 bit integers
	      if (bit_depth <= 2) then                                           
	        count := 1;                                                      
	      else                                                               
	        if(depth <= 1) then                                              
	 	       count := count;                                                
	 	     else                                                             
	 	       depth := depth / 2;                                            
	          count := count + 1;                                            
	 	     end if;                                                          
	 	   end if;                                                            
	   end loop;                                                             
	   return(count);        	                                              
	 end;                                                                    

	
	-- C_TRANSACTIONS_NUM is the width of the index counter for
	-- number of beats in a burst write or burst read transaction.
	 constant  C_TRANSACTIONS_NUM : integer := clogb2(C_M_AXI_BURST_LEN-1);

	-- //SECTION AXI4FULL signals
	--AXI4 internal temp signals
	signal axi_awaddr	: std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
	signal axi_awvalid	: std_logic;
	signal axi_wdata	: std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
	signal axi_wlast	: std_logic;
	signal axi_wvalid	: std_logic;
	signal axi_bready	: std_logic;
	signal axi_araddr	: std_logic_vector(C_M_AXI_ADDR_WIDTH-1 downto 0);
	signal axi_arvalid	: std_logic;
	signal axi_rready	: std_logic;
	--write beat count in a burst
	signal write_index	: std_logic_vector(7 downto 0);
	--read beat count in a burst
	signal read_index	: std_logic_vector(7 downto 0);
	--size of C_M_AXI_BURST_LEN length burst in bytes
	signal burst_size_bytes	: std_logic_vector(C_TRANSACTIONS_NUM+2 downto 0);
	--The burst counters are used to track the number of burst transfers of C_M_AXI_BURST_LEN burst length needed to transfer 2^C_MASTER_LENGTH bytes of data.
	-- signal write_burst_counter	: std_logic_vector(C_NO_BURSTS_REQ downto 0);
	-- signal read_burst_counter	: std_logic_vector(C_NO_BURSTS_REQ downto 0);

	signal start_single_burst_write	: std_logic;
	signal start_single_burst_read	: std_logic;

	signal writes_done	: std_logic;
	signal reads_done	: std_logic;
	-- signal error_reg	: std_logic;
	-- signal compare_done	: std_logic;
	-- signal read_mismatch	: std_logic;
	signal burst_write_active	: std_logic;
	signal burst_read_active	: std_logic;
	-- signal expected_rdata	: std_logic_vector(C_M_AXI_DATA_WIDTH-1 downto 0);
	--Interface response error flags
	-- signal write_resp_error	: std_logic;
	-- signal read_resp_error	: std_logic;
	signal wnext	: std_logic;
	signal rnext	: std_logic;

	signal init_write_txn_ff	: std_logic;
	signal init_write_txn_ff2	: std_logic;
	signal init_write_txn_pulse	: std_logic;

	signal init_read_txn_ff : std_logic;
	signal init_read_txn_ff2 : std_logic;
	signal init_read_txn_pulse : std_logic;

begin
	-----------------------------------------------------------------------------------------
	-- //SECTION I/O CONNECTIONS ASSIGNMENTS
	-----------------------------------------------------------------------------------------
	AXI_READ_DATA_O <= M_AXI_RDATA;
  AXI_READ_LAST_O  <= M_AXI_RLAST;
  AXI_WRITE_RDY_O  <= wnext;
  AXI_WRITE_DONE_O <= axi_bready and M_AXI_BVALID;
  AXI_READ_VLD_O   <= rnext;


	-----------------------------------------------------------------------------------------
	--I/O CONNECTIONS. WRITE ADDRESS (AW)
	-----------------------------------------------------------------------------------------
	--The AXI address is a concatenation of the target base address + active offset range
	M_AXI_AWADDR	<= std_logic_vector( unsigned(AXI_BASE_ADDRESS_I) + unsigned(axi_awaddr) );
	--Burst LENgth is number of transaction beats, minus 1
	M_AXI_AWLEN	<= std_logic_vector( to_unsigned(C_M_AXI_BURST_LEN - 1, 8) );
	--Size should be C_M_AXI_DATA_WIDTH, in 2^SIZE bytes, otherwise narrow bursts are used
	M_AXI_AWSIZE	<= std_logic_vector( to_unsigned(clogb2((C_M_AXI_DATA_WIDTH/8)-1), 3) );
	--INCR burst type is usually used, except for keyhole bursts
	M_AXI_AWBURST	<= "01";
	M_AXI_AWVALID	<= axi_awvalid;

	-----------------------------------------------------------------------------------------
	--WRITE DATA(W)
	-----------------------------------------------------------------------------------------
	M_AXI_WDATA	<= axi_wdata;
	--All bursts are complete and aligned in this example
	M_AXI_WSTRB	<= (others => '1');
	M_AXI_WLAST	<= axi_wlast;
	M_AXI_WVALID	<= axi_wvalid;
	M_AXI_WDATA	<= axi_wdata;
	-----------------------------------------------------------------------------------------
	--Write Response (B)
	-----------------------------------------------------------------------------------------
	M_AXI_BREADY	<= axi_bready;
	-----------------------------------------------------------------------------------------
	--READ ADDRESS (AR)
	-----------------------------------------------------------------------------------------
	M_AXI_ARADDR	<= std_logic_vector( unsigned( AXI_BASE_ADDRESS_I ) + unsigned( axi_araddr ) );
	--Burst length is number of transaction beats, minus 1
	M_AXI_ARLEN	<= std_logic_vector( to_unsigned(C_M_AXI_BURST_LEN - 1, 8) );
	--Size should be C_M_AXI_DATA_WIDTH, in 2^n bytes, otherwise narrow bursts are used
	M_AXI_ARSIZE	<= std_logic_vector( to_unsigned( clogb2((C_M_AXI_DATA_WIDTH/8)-1),3 ));
	--INCR burst type is usually used, except for keyhole bursts
	M_AXI_ARBURST	<= "01";
	M_AXI_ARVALID	<= axi_arvalid;
	-----------------------------------------------------------------------------------------
	--READ AND READ RESPONSE (R)
	-----------------------------------------------------------------------------------------
	M_AXI_RREADY	<= axi_rready;
	--Example design I/O
	-- TXN_DONE	<= compare_done;
	--Burst size in bytes
	burst_size_bytes	<= std_logic_vector( to_unsigned((C_M_AXI_BURST_LEN * (C_M_AXI_DATA_WIDTH/8)),C_TRANSACTIONS_NUM+3) );
	-----------------------------------------------------------------------------------------

	-----------------------------------------------------------------------------------------
	-- //SECTION Transaction initiation pulse
	-----------------------------------------------------------------------------------------

	-- //IMPORTANT When transaction starts it resets the whole logic for the start of the new transaction 
	init_write_txn_pulse <= ( not init_write_txn_ff2)  and  init_write_txn_ff;
	init_read_txn_pulse <= ( not init_read_txn_ff2 )  and  init_read_txn_ff ;

  --Generate a pulse to initiate AXI transaction.
  edge_detector_write:process(M_AXI_ACLK)
  begin
    if (rising_edge (M_AXI_ACLK)) then
      -- Initiates AXI transaction delay        
      if (M_AXI_ARESETN = '1') then
        init_write_txn_ff  <= '0';
        init_write_txn_ff2 <= '0';
      else
				-- NOTE Here starts the transaction, this code isolates transaction rising edge which enables all other processes
        init_write_txn_ff  <= axi_write_init_i;
        init_write_txn_ff2 <= init_write_txn_ff;
      end if;
    end if;
  end process;

  --Generate a pulse to initiate AXI transaction.
  edge_detector_read:process(M_AXI_ACLK)
  begin
    if (rising_edge (M_AXI_ACLK)) then
      -- Initiates AXI transaction delay        
      if (M_AXI_ARESETN = '1') then
        init_read_txn_ff  <= '0';
        init_read_txn_ff2 <= '0';
      else
        init_read_txn_ff  <= axi_read_init_i;
        init_read_txn_ff2 <= init_read_txn_ff;
      end if;
    end if;
  end process;
	-----------------------------------------------------------------------------------------
	-- //SECTION Write Address Channel
	-----------------------------------------------------------------------------------------

	-- The purpose of the write address channel is to request the address and 
	-- command information for the entire transaction.  It is a single beat
	-- of information.

	-- The AXI4 Write address channel in this example will continue to initiate
	-- write commands as fast as it is allowed by the slave/interconnect.
	-- The address will be incremented on each accepted address transaction,
	-- by burst_size_byte to point to the next address. 

	  process(M_AXI_ACLK)                                            
	  begin                                                                
	    if (rising_edge (M_AXI_ACLK)) then                                 
	      if (M_AXI_ARESETN = '1' or init_write_txn_pulse = '1') then                                   
	        axi_awvalid <= '0';                                            
	      else                                                             
	        -- // NOTE If previously not valid , start next transaction            
					-- // NOTE awvalid is being generated if state is WRITE, so always no specific dependecy 
	        if (axi_awvalid = '0' and start_single_burst_write = '1') then 
	          axi_awvalid <= '1';                                          
	          -- Once asserted, VALIDs cannot be deasserted, so axi_awvalid
	          -- must wait until transaction is accepted                   
	        elsif (M_AXI_AWREADY = '1' and axi_awvalid = '1') then         
	          axi_awvalid <= '0';                                          
	        else                                                           
	          axi_awvalid <= axi_awvalid;                                  
	        end if;                                                        
	      end if;                                                          
	    end if;                                                            
	  end process;                                                         

		axi_awaddr <= AXI_WRITE_ADDRESS_I;

	----------------------
	-- //SECTION Write Data Channel
	----------------------

	--// NOTE The write data will continually try to push write data across the interface.

	--The amount of data accepted will depend on the AXI slave and the AXI
	--Interconnect settings, such as if there are FIFOs enabled in interconnect.

	--Note that there is no explicit timing relationship to the write address channel.
	--The write channel has its own throttling flag, separate from the AW channel.

	-- //IMPORTANT Synchronization between the channels must be determined by the user.

	--The simpliest but lowest performance would be to only issue one address write
	--and write data burst at a time.

	--In this example they are kept in sync by using the same address increment
	--and burst sizes. Then the AW and W channels have their transactions measured
	--with threshold counters as part of the user logic, to make sure neither 
	--channel gets too far ahead of each other.

	-- //IMPORTANT Forward movement occurs when the write channel is valid and ready

	  wnext <= M_AXI_WREADY and axi_wvalid;                                       
		axi_wvalid <= AXI_WRITE_VLD_I;
	                                                                                    
	--WLAST generation on the MSB of a counter underflow                                
	-- WVALID logic, similar to the axi_awvalid always block above                      
	  process(M_AXI_ACLK)                                                               
	  begin                                                                             
	    if (rising_edge (M_AXI_ACLK)) then                                              
	      if (M_AXI_ARESETN = '1' or init_write_txn_pulse = '1') then                                                
	        axi_wlast <= '0';                                                           
	        -- axi_wlast is asserted when the write index                               
	        -- count reaches the penultimate count to synchronize                       
	        -- with the last write data when write_index is b1111                       
	        -- elsif (&(write_index[C_TRANSACTIONS_NUM-1:1])&& ~write_index[0] && wnext)
	      else                                                                          
					 -- IMPORTANT wlast needs write_index
					 -- BUG changed that write_index is converted to unsigned, comparison is done with unsigned values
					 -- BUG changed to C_M_AXI_BURST_LEN-1 because elaboration fails for -1 
	        if ((((unsigned(write_index) = to_unsigned(C_M_AXI_BURST_LEN-1,C_TRANSACTIONS_NUM+1)) and C_M_AXI_BURST_LEN >= 2) and wnext = '1') or (C_M_AXI_BURST_LEN = 1)) then
	          axi_wlast <= '1';                                                         
	          -- Deassrt axi_wlast when the last write data has been                    
	          -- accepted by the slave with a valid response                            
	        elsif (wnext = '1') then                                                    
	          axi_wlast <= '0';                                                         
	        elsif (axi_wlast = '1' and C_M_AXI_BURST_LEN = 1) then                      
	          axi_wlast <= '0';                                                         
	        end if;                                                                     
	      end if;                                                                       
	    end if;                                                                         
	  end process;                                                                      
	                                                                                    
	-- Burst length counter. Uses extra counter register bit to indicate terminal       
	-- count to reduce decode logic */                                                  
	  process(M_AXI_ACLK)                                                               
	  begin                                                                             
	    if (rising_edge (M_AXI_ACLK)) then                                              
	      if (M_AXI_ARESETN = '1' or start_single_burst_write = '1' or init_write_txn_pulse = '1') then               
	        write_index <= (others => '0');                                             
	      else                                                                          
	        if (wnext = '1' and (write_index /= std_logic_vector(to_unsigned(C_M_AXI_BURST_LEN-1,C_TRANSACTIONS_NUM+1)))) then                
	          write_index <= std_logic_vector(unsigned(write_index) + 1);                                         
	        end if;                                                                     
	      end if;                                                                       
	    end if;                                                                         
	  end process;                                                                      

		axi_wdata <= AXI_WRITE_DATA_I;
	                                                                                    
	------------------------------
	-- //SECTION Write Response (B) Channel
	------------------------------

	--The write response channel provides feedback that the write has committed
	--to memory. BREADY will occur when all of the data and the write address
	--has arrived and been accepted by the slave.

	--The write issuance (number of outstanding write addresses) is started by 
	--the Address Write transfer, and is completed by a BREADY/BRESP.

	--While negating BREADY will eventually throttle the AWREADY signal, 
	--it is best not to throttle the whole data channel this way.

	--The BRESP bit [1] is used indicate any errors from the interconnect or
	--slave for the entire write burst. This example will capture the error 
	--into the ERROR output. 

	  process(M_AXI_ACLK)                                             
	  begin                                                                 
	    if (rising_edge (M_AXI_ACLK)) then                                  
	      if (M_AXI_ARESETN = '1' or init_write_txn_pulse = '1') then                                    
	        axi_bready <= '0';                                              
	        -- accept/acknowledge bresp with axi_bready by the master       
	        -- when M_AXI_BVALID is asserted by slave                       
	      else                                                              
				  -- //NOTE bready depends on bvalid
	        if (M_AXI_BVALID = '1' and axi_bready = '0') then               
	          axi_bready <= '1';                                            
	          -- deassert after one clock cycle                             
	        elsif (axi_bready = '1') then                                   
	          axi_bready <= '0';                                            
	        end if;                                                         
	      end if;                                                           
	    end if;                                                             
	  end process;                                                          
	                                                                        
	                                                                        
	-- --Flag any write response errors                                        
	--   write_resp_error <= axi_bready and M_AXI_BVALID and M_AXI_BRESP(1);   


	------------------------------
	-- //SECTION Read Address Channel
	------------------------------

	--The Read Address Channel (AW) provides a similar function to the
	--Write Address channel- to provide the tranfer qualifiers for the burst.

	--In this example, the read address increments in the same
	--manner as the write address channel.

	  process(M_AXI_ACLK)										  
	  begin                                                              
	    if (rising_edge (M_AXI_ACLK)) then                               
	      if (M_AXI_ARESETN = '1' or init_read_txn_pulse = '1') then                                 
	        axi_arvalid <= '0';                                          
	     -- If previously not valid , start next transaction             
	      else                                                           
	        if (axi_arvalid = '0' and start_single_burst_read = '1') then
	          axi_arvalid <= '1';                                        
	        elsif (M_AXI_ARREADY = '1' and axi_arvalid = '1') then       
	          axi_arvalid <= '0';                                        
	        end if;                                                      
	      end if;                                                        
	    end if;                                                          
	  end process;                                                       
	                                                                     
		axi_araddr <= AXI_READ_ADDRESS_I;

	----------------------------------
	-- //SECTION Read Data (and Response) Channel
	----------------------------------

	 -- // NOTE Forward movement occurs when the channel is valid and ready   
	  rnext <= M_AXI_RVALID and axi_rready;                                 
	                                                                        
	                                                                        
	-- Burst length counter. Uses extra counter register bit to indicate    
	-- terminal count to reduce decode logic                                
	  process(M_AXI_ACLK)                                                   
	  begin                                                                 
	    if (rising_edge (M_AXI_ACLK)) then                                  
	      if (M_AXI_ARESETN = '1' or start_single_burst_read = '1' or init_read_txn_pulse = '1') then    
	        read_index <= (others => '0');                                  
	      else                                                              
	        if (rnext = '1' and (read_index <= std_logic_vector(to_unsigned(C_M_AXI_BURST_LEN-1,C_TRANSACTIONS_NUM+1)))) then   
	          read_index <= std_logic_vector(unsigned(read_index) + 1);                               
	        end if;                                                         
	      end if;                                                           
	    end if;                                                             
	  end process;                                                          

		axi_rready <= AXI_READ_RDY_I;
	                                                                        
  start_burst_logic : process(M_AXI_ACLK)
  begin
    if (rising_edge (M_AXI_ACLK)) then
      if (M_AXI_ARESETN = '1') then
        -- reset condition                                                                                   
        -- All the signals are ed default values under reset condition                                       
        start_single_burst_write <= '0';
        start_single_burst_read  <= '0';
      else
        -- state transition                                                                                  
        if (init_write_txn_pulse = '1' and start_single_burst_write = '0' and burst_write_active = '0') then  --axi_awvalid = '0' and 
          start_single_burst_write <= '1';
        else
          start_single_burst_write <= '0';  --Negate to generate a pulse                              
        end if;

        if (init_read_txn_pulse = '1' and start_single_burst_read = '0' and burst_read_active = '0') then  --axi_arvalid = '0'  and 
          start_single_burst_read <= '1';
        else
          start_single_burst_read <= '0';  --Negate to generate a pulse                               
        end if;
      end if;
    end if;
  end process;


  -- burst_write_active signal is asserted when there is a burst write transaction                           
  -- is initiated by the assertion of start_single_burst_write. burst_write_active                           
  -- signal remains asserted until the burst write is accepted by the slave                                  
  process(M_AXI_ACLK)
  begin
    if (rising_edge (M_AXI_ACLK)) then
      if (M_AXI_ARESETN = '1' or init_write_txn_pulse = '1') then
        burst_write_active <= '0';

      --The burst_write_active is asserted when a write burst transaction is initiated                      
      else
        if (start_single_burst_write = '1') then
          burst_write_active <= '1';
        elsif (M_AXI_BVALID = '1' and axi_bready = '1') then
          burst_write_active <= '0';
        end if;
      end if;
    end if;
  end process;


  -- burst_read_active signal is asserted when there is a burst write transaction                            
  -- is initiated by the assertion of start_single_burst_write. start_single_burst_read                      
  -- signal remains asserted until the burst read is accepted by the master                                  
  process(M_AXI_ACLK)
  begin
    if (rising_edge (M_AXI_ACLK)) then
      if (M_AXI_ARESETN = '1' or init_write_txn_pulse = '1') then
        burst_read_active <= '0';

      --The burst_write_active is asserted when a write burst transaction is initiated                      
      else
        if (start_single_burst_read = '1')then
          burst_read_active <= '1';
        elsif (M_AXI_RVALID = '1' and axi_rready = '1' and M_AXI_RLAST = '1') then
          burst_read_active <= '0';
        end if;
      end if;
    end if;
  end process;
	                                                                        
	-- Add user logic here

	-- User logic ends

end implementation;
