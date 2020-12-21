`include "myfilter.svh"
import myfilter_pkg::*;

program i2c_ctr_test
  
  (input logic clk,
   input logic 	rst_n,
   output logic clr_in,
   output logic next_in,
   output logic byteen_in, 
   input logic 	byteok_out,
   input logic 	frameok_out   
   );

   default clocking cb @(posedge clk);
     output clr_in;
     output next_in;
     output byteen_in; 
     input  byteok_out;
     input  frameok_out;
   endclocking
   
   initial
     begin : test_program

	$info("T1: RESET");	
	clr_in = '0;
	next_in = '0;
	byteen_in = '0;	
	wait(rst_n);
	##1;
	
	$info("T1: IDLE");			
	##2;
	
	$info("T2: COUNT");		

	for (int i = 0; i < I2C_FRAME_BYTES; ++i)
	  begin : byte_loop
	     if (i == 0)
	       cb.byteen_in <= '0;
	     else
	       cb.byteen_in <= '1;	       
	     for (int j = 0; j < 9; ++j)
	       begin : bit_loop
		  cb.next_in <= '1;	
		  ##1;
		  cb.next_in <= '0;
		  ##3;
		  if (j == 7)
		    T2_byteok: assert (cb.byteok_out == '1) else $error("byteok_out was not '1");
	       end : bit_loop
	  end : byte_loop
	T2_frameok: assert (cb.frameok_out == '1) else $error("frameok_out was not '1");
	
	$info("T3: CLR");		
	cb.clr_in <= '1;
	cb.next_in <= '1;
	cb.byteen_in <= '1;
	##1;

	$finish;
	
     end : test_program
   
endprogram


