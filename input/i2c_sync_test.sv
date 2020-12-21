`include "myfilter.svh"
import myfilter_pkg::*;
import i2c_pkg::*;

program i2c_sync_test
  
  (input logic clk,
   input logic rst_n,

   output logic sda_in,   
   output logic scl_in,

   input logic sda_out,
   input logic scl_out,

   input logic past_sda_out,
   input logic past_scl_out
   );

   default clocking cb @(posedge clk);
      output   sda_in;   
      output   scl_in;
      input    sda_out;
      input    scl_out;
      input    past_sda_out;
      input    past_scl_out;
   endclocking
   
   initial
     begin : test_program

	$info("T1: RESET");	
	sda_in = '1;
	scl_in = '1;
	wait(rst_n);
	
	// T2 - T5: I2C signals change on clk rising edge
	
	$info("T2: SDA FALL VIOL");		
	@(posedge clk);		
	sda_in = '0;
	#(I2C_CLOCK_PERIOD);

	$info("T3: SCL FALL VIOL");		
	@(posedge clk);		
	scl_in = '0;
	#(I2C_CLOCK_PERIOD);	

	$info("T4: SDA RISE VIOL");
	@(posedge clk);		
	sda_in = '1;
	#(I2C_CLOCK_PERIOD);

	$info("T5: SCL RISE VIOL");				
	@(posedge clk);		
	scl_in = '1;
	#(I2C_CLOCK_PERIOD);	

	// T6 - T9: I2C signals change on clk falling edge

	$info("T6: SDA FALL");		
	@(negedge clk);		
	sda_in = '0;
	#(I2C_CLOCK_PERIOD);

	$info("T7: SCL FALL");		
	@(negedge clk);		
	scl_in = '0;
	#(I2C_CLOCK_PERIOD);	

	$info("T8: SDA RISE");
	@(negedge clk);		
	sda_in = '1;
	#(I2C_CLOCK_PERIOD);

	$info("T9: SCL RISE");				
	@(negedge clk);		
	scl_in = '1;
	#(I2C_CLOCK_PERIOD);	

	$info("T10: RANDOM");					
	repeat(100)
	  begin
	     { scl_in, sda_in } = $urandom;
	     @(negedge clk);		
	  end
	$finish;
	
     end : test_program
   
endprogram


