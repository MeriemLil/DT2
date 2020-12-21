`include "myfilter.svh"

import myfilter_pkg::*;

program cmem_test
  (input logic clk,
   input logic 			       rst_n,
   output logic 		       sde_in,
   output logic 		       sd_in,
   input logic 			       sd_out,
   output logic [$clog2(CMEMSIZE)-1:0] addr_in,
   input logic [DATABITS-1:0] 	       d_out
   );

   default clocking cb @(posedge clk);
     output sde_in;
     output sd_in;
     input  sd_out;
     output addr_in;
     input  d_out;
   endclocking

   initial
     begin : test_program
	logic [CMEMSIZE-1:0][DATABITS-1:0] wdata;	
	logic [DATABITS-1:0] rdata;	
	
	$info("T1: RESET");	
	sde_in <= '0;
	sd_in <= '0;
	addr_in <= '0;	
	wait(rst_n);
	##1;
	
	$info("T2: SERIAL WRITE");
	for (int i = 0; i < CMEMSIZE; ++i)	
	  wdata[i] = $urandom;

	cb.sde_in <= '1;
	cb.addr_in <= 0;

	fork

	   begin : write_side // CMEMSIZE*DATABITS shift + 1 idle cycle
	      for (int i = 0; i < CMEMSIZE; ++i)
		begin
		   for (int j=0; j < DATABITS; ++j)
		     begin
			cb.sd_in <= wdata[CMEMSIZE-i-1][DATABITS-1-j];
			##1;
			$info("%d", j);		  
		     end
		end
	      cb.sde_in <= '0;
	      ##1;
	   end : write_side
	   
	   begin : read_side // 1 idle cycle + on read after each CMEMSIZE*DATABITS cycles
	      ##1;
	      for (int i = 0; i < CMEMSIZE; ++i)
		begin
		   ##(DATABITS);
		   rdata = cb.d_out;
		   T2_read: assert (rdata == wdata[CMEMSIZE-i-1]) else $error("T2: wrote %b, got %b", wdata[CMEMSIZE-i-1], rdata);
		end
	   end : read_side
	join
	##1;

	$info("T3: ADDRESSED READ");			
	for (int i = 0; i <= CMEMSIZE; ++i) // One extra cycle for reading cb
	  begin
	     if (i < CMEMSIZE)
	       cb.addr_in <= i;
	     if (i > 0)
	       begin
		  rdata = cb.d_out;
		  T3_read: assert (rdata == wdata[i-1]) else $error("T3: expected %h, got %h", wdata[i-1], rdata);
	       end
	     ##1;
	  end
	##1;	

	$info("T4: SERIAL READ");
	for (int i = 0; i < CMEMSIZE; ++i)
	  begin
	     cb.sde_in <= '1;
	     rdata = '0;
	     for (int j=0; j < DATABITS; ++j)
	       begin
		  ##1;
		  rdata = { rdata[DATABITS-2:0], cb.sd_out };
	       end
	     T4_read: assert (rdata == wdata[CMEMSIZE-i-1]) else $error("T4: expected %b got %b", wdata[CMEMSIZE-i-1], rdata);
	  end

	cb.sde_in <= '0;
	##1;
	
	$finish;
	
     end : test_program
   
   
endprogram 

