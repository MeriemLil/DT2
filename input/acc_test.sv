`include "myfilter.svh"
import myfilter_pkg::*;

program acc_test
  (input logic clk,
   input logic 		      rst_n,
   output 		      acc_cmd_t cmd_in,
   output logic [ACCBITS-1:0] d_in,
   input logic [ACCBITS-1:0]  d_out,
   input logic [DATABITS-1:0] ext_out
   );

   default clocking cb @(posedge clk);
      output cmd_in;
      output d_in;
      input  d_out;
      input  ext_out;
   endclocking
   
   initial
     begin : test_program
	logic [ACCBITS-1:0] wdata;
	
	$info("T1: RESET");
	cmd_in = ACC_NOP;
	d_in = '0;
	
	wait(rst_n);
	##1;

	$info("T2: ACC_LOAD");
	wdata = '1;
	cb.cmd_in <= ACC_LOAD;
	cb.d_in <= wdata;
	##2;
	T2_loadones: assert (cb.d_out == wdata) else $error("T2: d_out value not all 1:s");
	wdata = $urandom;
	cb.d_in <= wdata;
	##2;
	T2_loadrand: assert (cb.d_out == wdata) else $error("T2: d_out value not same as written value.");
	T2_extcheck: assert (cb.ext_out == wdata[DATABITS-1:0]) else $error("T2: ext_out value wrong");	

	##1;
	$info("T3: ACC_CLEAR");

	cb.cmd_in <= ACC_CLEAR;
	##2;
	T3_clear: assert (cb.d_out == 0) else $error("T4: d_out value wrong");

	##1;

	$finish;
	
     end : test_program

endprogram


