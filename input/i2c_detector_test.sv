`include "myfilter.svh"
import myfilter_pkg::*;

program i2c_detector_test
  (
   input logic 	clk,
   input logic 	rst_n,

   output logic sda_in,
   output logic scl_in,
   output logic past_sda_in,
   output logic past_scl_in,

   input logic 	start_out,
   input logic 	stop_out,
   input logic 	scl_rise_out,
   input logic 	scl_fall_out
   );

   initial
     begin : test_program
	scl_in = '1;
	past_scl_in = '1;
	sda_in = '1;
	past_sda_in = '1;
	 @(posedge clk);

	$info("T1: START");
	sda_in = '0;
	 @(posedge clk);
	past_sda_in = '0;	
	scl_in = '0;
	 @(posedge clk);

	$info("T2: SCL RISE");
	past_scl_in = '0;	
	scl_in = '1;
	 @(posedge clk);

	$info("T3: SCL FALL");	
	past_scl_in = '1;		
	scl_in = '0;
	 @(posedge clk);
	past_scl_in = '0;			
	scl_in = '1;
	 @(posedge clk);

	$info("T4: STOP");	
	past_scl_in = '1;					
	sda_in = '1;
	@(posedge clk);
	past_sda_in = '1;	
	 @(posedge clk);

	$info("T5: RANDOM");	
	{ scl_in, sda_in, past_scl_in, past_sda_in } = '1;
	repeat(100)
	  begin
	     past_scl_in = scl_in;
	     past_sda_in = sda_in;	     
	     { scl_in, sda_in } = $urandom;
	     @(posedge clk);
	  end
	$finish;
	
     end : test_program

endprogram

