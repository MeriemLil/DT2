`include "myfilter.svh"
import myfilter_pkg::*;

program i2c_srg_test
  
  (input logic clk,
   input logic 	rst_n,
   output logic clr_in,
   output logic next_in,
   output logic bit_in,
   input logic 	bit_out,
   input logic 	addrok_out
   );

   default clocking cb @(posedge clk);
      output 	clr_in;
      output    next_in;
      output    bit_in;
      input     bit_out;
      input 	addrok_out;
   endclocking
   
   initial
     begin : test_program
	logic [7:0] input_byte;
	logic [7:0] output_byte;	
	logic 	    addrok;
	
	$info("T1: RESET");	
	input_byte = '0;
	output_byte = '0;
	addrok = '0;
	next_in = '0;
	clr_in = '0;
	bit_in = '0;
	wait(rst_n);
	##1;
	
	$info("T2: IDLE");	
	bit_in = '1;
	##2;
	
	$info("T3: SHIFT 8x1");	
	next_in = '1;
	##8;

	$info("T4: SHIFT 8x0");	
	bit_in = '0;	
	##8;

	$info("T5: RAND");		
	repeat(10)
	  begin
	     input_byte = $urandom;
	     output_byte = '0;
	     for (int i=0; i < 9; ++i)
	       begin
		  if (i < 8)
		    bit_in = input_byte[7-i];
		  if (i > 0)
		    output_byte = { output_byte[6:0], bit_out };
		  addrok = addrok_out;
		  ##1;
	       end
	     T5_bit_out: assert (input_byte == output_byte)
	       else $error("T5: %b => %b", input_byte, output_byte);
	     T5_addrok: assert (addrok == ((input_byte[7:1] == I2C_ADDRESS) ? '1 : '0))
	       else $error("T5: addrok_out in wrong state");

	     bit_in = '1;	     
	     clr_in = '1;
	     ##1;
	     clr_in = '0;
	  end

	$info("T6: I2C_ADDRESS");			
	input_byte = { I2C_ADDRESS, '0 };
	for (int i=0; i < 9; ++i)
	  begin
	     if(i < 8)
	       bit_in = input_byte[7-i];
	     if (i > 0)
	       output_byte = { output_byte[6:0], bit_out };
	     addrok = addrok_out;
	     ##1;
	  end
	T6_addrok: assert (addrok == '1)
	  else $error("T6: addrok_out != '1");
	
	$finish;
	
     end : test_program
  
endprogram


