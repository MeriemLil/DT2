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
	cb.scl_fall_in <= '0;
	cb.byteok_in <= '0;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;

	
	$info("T6: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-a-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	//cb.lastbit_in <= '0;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;
	cb.addrok_in <= '0;
	cb.scl_fall_in <= '0;
	
	
	
	$info("T7: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-b-d-e-g-TACK-a-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	cb.lastbit_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;
	cb.addrok_in <= '0;
	cb.scl_fall_in <= '0;
	


	$info("T8: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-b-d-e-g-TACK-b-c-f-TX-a-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	cb.lastbit_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	cb.scl_fall_in <= '0;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;
	cb.addrok_in <= '0;


	$info("T9: IDLE-a-HRX-b-d-e-HACK-b-c-e-j-RX-b-d-e-g-RACK-b-c-e-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.scl_fall_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.frameok_in <= '1;
	##1;
	cb.frameok_in <= '0;
	cb.addrok_in <= '0;
	cb.scl_fall_in <= '0;


	$info("T10: IDLE-a-HRX-b-d-e-HACK-b-c-e-j-RX-a-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.scl_fall_in <= '0;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;
	cb.addrok_in <= '0;

	
	$info("T11: IDLE-a-HRX-b-d-e-HACK-b-d-g-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	cb.scl_fall_in <= '0;
	

	$info("T12: IDLE-a-HRX-b-d-e-HACK-b-d-h-HACK-b-c-f-HACK-a-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	##1;
	cb.addrok_in <= '1;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;
	cb.addrok_in <= '0;

	
	$info("T13: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-b-d-e-g-TACK-a-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	cb.lastbit_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;
	cb.addrok_in <= '0;
	cb.scl_fall_in <= '0;


	$info("T14: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-b-d-e-g-TACK-b-c-f-TX");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	cb.lastbit_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '0;

	

	$info("T15: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-b-c-TX-b-d-f-TX-b-d-e-h-TX");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	cb.lastbit_in <= '0;
	cb.scl_rise_in <= '1;
	##1;
	cb.scl_rise_in <= '0;
	cb.addrok_in <= '0;
	cb.scl_fall_in <= '0;
	

	$info("T16: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-b-c-TX-b-d-f-TX-b-d-e-h-TX-a-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	cb.lastbit_in <= '0;
	cb.scl_rise_in <= '1;
	##1;
	cb.scl_rise_in <= '0;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;
	cb.addrok_in <= '0;
	

	$info("T17: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-b-d-e-g-TACK-b-d-TACK");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	cb.lastbit_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.addrok_in <= '0;
	cb.scl_fall_in <= '0;
	

	$info("T18: IDLE-a-HRX-b-d-e-HACK-b-c-e-j-RX-b-c-RX-b-d-e-g-RACK-a-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.scl_rise_in <= '1;
	##1;
	cb.scl_rise_in <= '0;
        cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.stop_in <= '1;
	##1;
	cb.stop_in <= '0;
	cb.addrok_in <= '0;

	
   	$info("T19: IDLE-a-HRX-b-d-e-HACK-b-c-e-i-TX-b-d-e-g-TACK-b-c-IDLE");
	cb.start_in <= '1;
	##1;
	cb.start_in <= '0;
	cb.byteok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '0;
	cb.addrok_in <= '1;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.lastbit_in <= '1;
	##1;
	cb.lastbit_in <= '0;
	cb.scl_fall_in <= '1;
	##1;
	//cb.scl_fall_in <= '0;
	cb.byteok_in <= '1;
	##1;
	cb.byteok_in <= '0;
	cb.scl_fall_in <= '1;
	cb.frameok_in <= '1;
	##1;
	cb.frameok_in <= '0;
	cb.addrok_in <= '0;
	cb.scl_fall_in <= '0;


	
	$finish;
	
     end : test_program
   
   
endprogram

