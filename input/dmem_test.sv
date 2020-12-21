`include "myfilter.svh"
import myfilter_pkg::*;

program dmem_test
  (
   input logic 			       clk,
   input logic 			       rst_n,
   output logic 		       sde_in,
   output logic 		       sd_in,
   input logic 			       sd_out,
   output 			       dmem_cmd_t cmd_in,
   output logic [$clog2(DMEMSIZE)-1:0] addr_in,
   output logic [DATABITS-1:0] 	       d_in,
   output logic [DATABITS-1:0] 	       ext_in, 
   input logic [DATABITS-1:0] 	       d_out
   );

   default clocking cb @(posedge clk);
      output sde_in;
      output sd_in;
      input sd_out;
      output cmd_in;
      output addr_in;
      output d_in;
      output ext_in; 
      input d_out;
   endclocking
   
   initial
     begin : test_program
	logic [DMEMSIZE-1:0][DATABITS-1:0] wdata;	
	logic [DATABITS-1:0] rdata;	
	
	$info("T1: RESET");	
	sde_in = '0;
	sd_in = '0;
	cmd_in = DMEM_READ;
	addr_in = '0;
	d_in = '0;
	ext_in = '0;
	wait(rst_n);
	##1;
	
	$info("T2: SERIAL WRITE");	

	for (int i = 0; i < DMEMSIZE; ++i)	
	  wdata[i] = $urandom;

	cb.sde_in <= '1;
	cb.addr_in <= 0;
	cb.cmd_in <= DMEM_WRITE;

	fork

	   begin : write_side // DMEMSIZE*DATABITS shift + 1 idle cycle
	      for (int i = 0; i < DMEMSIZE; ++i)
		begin
		   cb.d_in <= wdata[i];
		   for (int j=0; j < DATABITS; ++j)
		     begin
			cb.sd_in <= wdata[DMEMSIZE-i-1][DATABITS-1-j];
			##1;
			$info("%d", j);		  
		     end
		end
	      cb.sde_in <= '0;
	      cb.cmd_in <= DMEM_READ;
	      ##1;
	   end : write_side

	   begin : read_side
	      ##1;
	      for (int i = 0; i < DMEMSIZE; ++i)
		begin
		   ##(DATABITS);
		   rdata = cb.d_out;
		   T2_read: assert (rdata == wdata[DMEMSIZE-i-1]) else $error("T2: wrote %b, got %b", wdata[DMEMSIZE-i-1], rdata);
		end
	      
	   end : read_side
	join
	##1;

	$info("T3: ADDRESSED READ");			
	for (int i = 0; i <= DMEMSIZE; ++i)
	  begin
	     if (i < DMEMSIZE)
	       cb.addr_in <= i;
	     if (i > 0)
	       begin
		  rdata = cb.d_out;
		  T3_read: assert (rdata == wdata[i-1]) else $error("T3: expected %b, got %b", wdata[i-1], rdata);
	       end
	     ##1;
	  end
	##1;
	
	$info("T4: SERIAL READ");
	for (int i = 0; i < DMEMSIZE; ++i)
	  begin
	     cb.sde_in <= '1;
	     rdata = '0;
	     for (int j=0; j < DATABITS; ++j)
	       begin
		  ##1;
		  rdata = { rdata[DATABITS-2:0], cb.sd_out };
	       end
	     T4_read: assert (rdata == wdata[DMEMSIZE-i-1]) else $error("T4: expected %b got %b", wdata[DMEMSIZE-i-1], rdata);
	  end
	cb.sde_in <= '0;
	##1;

	
	$info("T5: ADDRESSED WRITE");			
	for (int i = 0; i <= DMEMSIZE; ++i)
	  begin
	     if (i < DMEMSIZE)
	       begin
		  cb.addr_in <= i;
		  cb.d_in <= wdata[i];
		  cb.cmd_in <= DMEM_WRITE;
		  ##1;
	       end
	     if (i > 0)
	       begin
		  cb.addr_in <= i-1;		  
		  cb.cmd_in <= DMEM_READ;
		  ##1;
		  ##1;
		  rdata = cb.d_out;
		  T5_write: assert (rdata == wdata[i-1]) else $error("T5: Wrote %h, read %h", wdata[i-1], rdata);	     
	       end
	  end
	##1;
	

	$info("T6: CLEAR");			
	cb.cmd_in <= DMEM_CLEAR;
	##1;
	
	for (int i = 0; i <= DMEMSIZE; ++i)
	  begin
	     if (i < DMEMSIZE)
	       begin
		  cb.cmd_in <= DMEM_READ;
		  cb.addr_in <= i;
	       end
	     if (i > 0)
	       begin
		  rdata = cb.d_out;
		  T6_clear: assert (rdata == 0) else $error("T6: read %h form address %d, expected 0", rdata, cb.addr_in);	     
	       end
	     ##1;
	  end
	##1;
	
	$info("T7: PARALLEL SHIFT");			
	for (int i = 0; i < DMEMSIZE; ++i)
	  begin
	     cb.d_in <= '0;
	     cb.ext_in <= wdata[i];
	     cb.cmd_in <= DMEM_SHIFT;
	     ##1;
	     cmd_in <= DMEM_READ;
	     for (int j=0; j <= i; ++j)
	       begin
		  cb.addr_in <= j;
		  ##2;
		  rdata = cb.d_out;
		  T6_shift: assert (rdata == wdata[i-j]) else $error("T6: Shifted %h, read %h", wdata[i-j], rdata);	     
	       end
	  end
	
	$finish;
	
     end : test_program
   
   

endprogram 

