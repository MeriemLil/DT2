`include "myfilter.svh"


import myfilter_pkg::*;
import i2c_pkg::*;

program i2c_slave_test
  
  (input logic clk,
   input logic 	rst_n,
   inout tri1 	scl_inout,
   inout tri1 	sda_inout,
   input logic 	sde_out,
   input logic 	sd_out,
   output logic sd_in,
   input logic 	ul_out,
   input logic 	dl_out   
   );

   logic scl_read;
   logic scl_write;
   logic sda_read;
   logic sda_write;
   
   // Connect read and write variables
   assign scl_read = scl_inout;
   assign scl_inout = scl_write;
   assign sda_read = sda_inout;
   assign sda_inout = sda_write;
   
   initial
     begin : test_program
	logic [7:0] tx_byte;
	logic [7:0] rx_byte;	

	tx_byte = { I2C_ADDRESS, 1'b0 };

	fork
	   begin : bus_master

	      // This fork thread drives the I2C bus
	      
	      scl_write = 'z;
	      sda_write = 'z;

	      // Start action exactly on clock edge to test synchronizer
	      #1us;
	      @(posedge clk);
	      
	      
	      // START
	      $info("I2C START");
	      
	      sda_write = '0;
	      #(I2C_CLOCK_PERIOD/2.0);
	      scl_write = '0;
	      
	      $info("TX HEADER");	
	      for (int i = 7; i >= 0; --i)
		begin
		   if (tx_byte[i] == '1)
		     sda_write = 'z;
		   else
		     sda_write = '0;	       
		   #(I2C_CLOCK_PERIOD/2.0);
		   scl_write = 'z;
		   #(I2C_CLOCK_PERIOD/2.0);
		   scl_write = '0;	     
		end
	      
	      $info("ACK");
	      sda_write = 'z;
	      
	      #(I2C_CLOCK_PERIOD/2.0);
	      scl_write = 'z;
	      header_ack: assert(sda_read == '0) else $error("ACK != '0");	      
	      #(I2C_CLOCK_PERIOD/2.0);	
	      scl_write = '0;
	      
	      $info("TX BYTE");	
	      tx_byte = 8'b11101011;
	      for (int i = 7; i >= 0; --i)
		begin
		   if (tx_byte[i] == '1)
		     sda_write = 'z;
		   else
		     sda_write = '0;	       
		   #(I2C_CLOCK_PERIOD/2.0);
		   scl_write = 'z;
		   #(I2C_CLOCK_PERIOD/2.0);
		   scl_write = '0;	     
		end
	      
	      $info("ACK");
	      sda_write = 'z;
	      
	      #(I2C_CLOCK_PERIOD/2.0);
	      scl_write = 'z;
	      data_ack: assert(sda_read == '0) else $error("ACK != '0");	      
	      #(I2C_CLOCK_PERIOD/2.0);	
	      

	      $info("I2C STOP");
	      scl_write = '0;
	      sda_write = '0;		

	      #(I2C_CLOCK_PERIOD/2.0);
	      scl_write = 'z;
	      #(I2C_CLOCK_PERIOD/2.0);
	      sda_write = 'z;		
	      #(I2C_CLOCK_PERIOD/2.0);
	   end : bus_master
	   
	   begin : output_reader

	      // This fork thread 'listens' to the data outputs	

	      sd_in = '0;

	      forever
		begin
		   repeat(8)
		     begin
			@(posedge clk iff sde_out == '1)
			  begin
			     rx_byte = { rx_byte[6:0], sd_out };
			  end
		     end
		   rx_check: assert(tx_byte == rx_byte) else $error("tx_byte = %b, rx_byte = %b", tx_byte, rx_byte);
		end

 	   end : output_reader

	join_any
	
	$finish;	
     end : test_program

        
   
endprogram

