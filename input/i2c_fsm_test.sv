`include "myfilter.svh"
import myfilter_pkg::*;

program i2c_fsm_test
  
  (input logic clk,
   input logic 	rst_n,
   output logic start_in,
   output logic stop_in,
   output logic scl_rise_in,
   output logic scl_fall_in,
   output logic addrok_in,
   output logic byteok_in,
   output logic frameok_in,
   output logic lastbit_in,
   input logic 	ul_out,
   input logic 	dl_out,
   input logic 	byteen_out, 
   input logic 	sde_out, 
   input logic 	clr_out, 
   input logic 	next_out,
   input logic 	oe_out,
   input logic 	osel_out,
   input logic 	ack_out
   );

   default clocking cb @(posedge clk);
      output 	start_in;
      output 	stop_in;
      output 	scl_rise_in;
      output 	scl_fall_in;
      output 	addrok_in;
      output 	byteok_in;
      output 	frameok_in;
      output 	lastbit_in;
      input 	ul_out;
      input 	dl_out;
      input 	byteen_out; 
      input 	sde_out; 
      input 	clr_out; 
      input 	next_out;
      input 	oe_out;
      input 	osel_out;
      input 	ack_out;
   endclocking
   
   initial
     begin : test_program
	$info("T1: RESET");
	start_in = '0;
	stop_in = '0;
	scl_rise_in = '0;
	scl_fall_in = '0;
	addrok_in = '1;
	byteok_in = '0;
	frameok_in = '0;
	lastbit_in = '0;						
	wait(rst_n);
	##1;

	$info("T2: IDLE-a-HRX-a-IDLE");	
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;	
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;	
	
	$info("T3: IDLE-a-HRX-b-c-HRX-a-IDLE");	
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;	
	cb.scl_rise_in <= '1;
	##1;
	cb.scl_rise_in <= '0;	
	cb.stop_in <= '1;	
	##1;
	cb.stop_in <= '0;	

	$info("T4: IDLE-a-HRX-b-d-f-HRX-a-IDLE");	
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;	
	##1;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;	

	$info("T5: IDLE-a-HRX-b-d-e-HACK-a-IDLE");	
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;	
	cb.scl_fall_in <= '1;
	cb.byteok_in <= '1;	
	##1;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;		
	
	$finish;
	
     end : test_program
   
   
endprogram

