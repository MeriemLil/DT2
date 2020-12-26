`include "myfilter.svh"


import myfilter_pkg::*;

program i2c_slave_test
  
  (input logic clk,
   input logic 	rst_n,
   i2c_if i2c_bus,
   input logic 	sde_out,
   input logic 	sd_out,
   output logic sd_in,
   input logic 	ul_out,
   input logic 	dl_out   
   );

   enum logic [0:0] { M2S, S2M } packet_type; // Packet type indicator
   logic [7:0] m2s_tx_byte = '0;  // Master-to-slave byte tranmitted
   logic [7:0] m2s_rx_byte = '0;  // Master-to-slave byte received
   logic [7:0] s2m_tx_byte = '0;  // Slave-to-master byte tranmitted
   logic [7:0] s2m_rx_byte = '0;  // Slave-to-master byte received
   int 	       bit_counter = 0;   // serial_if uses this to count up to 8-bits 
   int 	       packet_bytes = 0;  // Number of bytest the serial_if side should expect
   int 	       byte_counter = 0;  // serial_if uses this to count bytes it has seen
   logic [6:0] i2c_address;       // i2c_address use for transmission
   logic       i2c_mode;          // R/W mode bit used for transmission
   
   initial
     begin : test_program

	logic ack;

	sd_in = '0;
	
	// Start action exactly on clock edge to test synchronizer

	wait(rst_n);
	@(posedge clk);
	
	fork
	   begin : bus_master  // This fork process drives the I2C bus
	      
	      ////////////////////////////////////////////////////////////////
	      // T1: Header only
	      ////////////////////////////////////////////////////////////////
	      
	      $info("T1 Header Only");
	      packet_type = M2S;         // Either M2S (master-to-slave) or S2M (slave-to-master)
	      packet_bytes = 1;          // How many bytes are transmitted
	      bit_counter = '0;          // Bit and byte counters should be reset before tests
	      byte_counter = 0;
	      i2c_address = I2C_ADDRESS; // I2C slave address
	      i2c_mode = '0;             // R/W mode bit 
	      ack = '1;                  // Set ack = '1 always before reading ACK bit from the bus
	      
	      i2c_bus.start_condition;
	      m2s_tx_byte = { i2c_address, i2c_mode };
	      i2c_bus.write_bit(m2s_tx_byte[7]);
	      i2c_bus.write_bit(m2s_tx_byte[6]);        
	      i2c_bus.write_bit(m2s_tx_byte[5]);        
	      i2c_bus.write_bit(m2s_tx_byte[4]);        
	      i2c_bus.write_bit(m2s_tx_byte[3]);        
	      i2c_bus.write_bit(m2s_tx_byte[2]);        
	      i2c_bus.write_bit(m2s_tx_byte[1]);
	      i2c_bus.write_bit(m2s_tx_byte[0]);        	      	      
	      i2c_bus.read_bit(ack);
	      i2c_bus.stop_condition;		      
	      T1_ack: assert (ack == '0) else $error("T1: ack != '0");
	      #100us;

	      ////////////////////////////////////////////////////////////////
	      // T2: Header only, wrong address
	      ////////////////////////////////////////////////////////////////

	      $info("T2 Header, wrong addr");
	      packet_type = M2S;
	      packet_bytes = 1;
	      byte_counter = 0;
	      bit_counter = '0;
	      i2c_address = I2C_ADDRESS ^ 8'b11111111; // Invert bits in address
	      i2c_mode = '0;
	      ack = '1;
	      
	      // To do: Add test
	      i2c_bus.start_condition;
	      m2s_tx_byte = { i2c_address, i2c_mode };
	      i2c_bus.write_byte(m2s_tx_byte);
	      i2c_bus.read_bit(ack);
	      i2c_bus.stop_condition;		      
	      T2_ack: assert (ack == '0) else $error("T2: ack != '0");
	      #100us;

	      
	      ////////////////////////////////////////////////////////////////
	      // T3: Write Frame
	      ////////////////////////////////////////////////////////////////
	      
	      $info("T3 Write Frame");
	      packet_type = M2S;
	      packet_bytes = I2C_DATA_BYTES;
	      byte_counter = 0;
	      bit_counter = '0;
	      i2c_address = I2C_ADDRESS;
	      i2c_mode = '0;

	      // To do: Add test	      
	      i2c_bus.start_condition;
	      m2s_tx_byte = { i2c_address, i2c_mode };
	      for (int i = I2C_DATA_BYTES - 1; i >= 0 ; i = i - 1)
		begin
	          i2c_bus.write_byte(m2s_tx_byte);
		  i2c_bus.read_bit(ack);		  
		end
	      i2c_bus.stop_condition;		      
	      T3_ack: assert (ack == '0) else $error("T3: ack != '0");
	      #100us;	      

	      ////////////////////////////////////////////////////////////////
	      // T4: Read Frame
	      ////////////////////////////////////////////////////////////////

	      $info("T4 Read Frame");
	      packet_type = S2M;
	      packet_bytes = I2C_DATA_BYTES;
	      byte_counter = 0;
	      bit_counter = '0;
	      i2c_address = I2C_ADDRESS;
	      i2c_mode = '1;

	      // To do: Add test
	      i2c_bus.start_condition;
	      s2m_tx_byte = { i2c_address, i2c_mode };
	      for (int i = I2C_DATA_BYTES - 1; i >= 0 ; i = i - 1)
		begin
	          i2c_bus.read_byte(s2m_rx_byte);
		end
	      i2c_bus.read_bit(ack);
	      i2c_bus.stop_condition;		      
	      T4_ack: assert (ack == '0) else $error("T4: ack != '0");
	      #100us;

	      
	   end : bus_master

	   
	   begin : serial_if // This fork process drives the serial interface

	      forever
		begin
		   if (byte_counter < packet_bytes)
		     sd_in = s2m_tx_byte[7-bit_counter];
		   else
		     sd_in = '1;
		   @(negedge clk);
		   if (sde_out)
		     begin
			m2s_rx_byte = { m2s_rx_byte[6:0] , sd_out };
			bit_counter = bit_counter + 1;
			if (bit_counter == 8)
			  begin
			     if (packet_type == M2S && i2c_address == I2C_ADDRESS)
			       M2S_check: assert(m2s_tx_byte == m2s_rx_byte)
				 else $error("M2S: %b => %b", m2s_tx_byte, m2s_rx_byte);
			     bit_counter = 0;
			     byte_counter = byte_counter + 1;
			  end
		     end
		end
 	   end : serial_if
	   
	join_any
	$finish;
        
     end : test_program
   
endprogram

