`include "myfilter.svh"
import myfilter_pkg::*;

program filter_unit_test
  
  (input logic clk,
   input logic 		       rst_n,
   output logic 	       sde_in,
   output logic 	       sd_in, 
   input logic 		       sd_out, 
   output logic 	       ul_in,
   output logic 	       dl_in, 
   output logic [DATABITS-1:0] ext_in,
   output logic 	       extready_in,
   input logic [DATABITS-1:0]  ext_out,
   input logic 		       extvalid_out
   );

   default clocking cb @(posedge clk);
      output  sde_in;
      output sd_in; 
      input  sd_out; 
      output ul_in;
      output dl_in; 
      output ext_in;
      output extready_in;
      input  ext_out;
      input  extvalid_out;
   endclocking
   
   initial
     begin : test_program
	logic [NTAPS-1:0][DATABITS-1:0] coeffs;
	logic [(CMEMSIZE+DMEMSIZE)-1:0][DATABITS-1:0] wdata;	
	logic [DATABITS-1:0] rdata;	
	logic 		     test_done = '0;

	case (NTAPS)
	  5:
	    begin
	       coeffs[0] = K4;
	       coeffs[1] = K2;
	       coeffs[2] = K;
	       coeffs[3] = K2;
	       coeffs[4] = K4;	     
	    end
	  7:
	    begin
	       coeffs[0] = K8;
	       coeffs[1] = K4;
	       coeffs[2] = K2;
	       coeffs[3] = K;
	       coeffs[4] = K2;
	       coeffs[5] = K4;	     
	       coeffs[6] = K8;	     	       
	    end

	  9:
	    begin
	       coeffs[0] = K16;
	       coeffs[1] = K8;
	       coeffs[2] = K4;
	       coeffs[3] = K2;
	       coeffs[4] = K;
	       coeffs[5] = K2;	     
	       coeffs[6] = K4;
	       coeffs[7] = K8;	     	       
	       coeffs[8] = K16;	     	       	       
	    end
	endcase

	//////////////////////////////////////////////////////////////////////////////////////
	// T1: Reset
	//////////////////////////////////////////////////////////////////////////////////////
	
	$info("T1: RESET");
	
	sde_in = '0;
	sd_in = '0;
	ext_in = '0;
	ul_in = '0;
	dl_in = '0;
	extready_in = '0;
	wait(rst_n);
	##1;

	//////////////////////////////////////////////////////////////////////////////////////
	// T2: Serial write and read
	//////////////////////////////////////////////////////////////////////////////////////

	fork
	   begin : control_inputs

	      $info("T2: SERIAL WRITE-READ");	      
	      sde_in = '1;
	      ul_in = '1;
	      dl_in = '0;
	      for (int i = 0; i < CMEMSIZE+DMEMSIZE; ++i)	
		wdata[i] = $urandom;
	      ##1;
	      
	      for (int i = 0; i < CMEMSIZE+DMEMSIZE; ++i)
		begin
		   for (int j=0; j < DATABITS; ++j)
		     begin
			sd_in = wdata[CMEMSIZE+DMEMSIZE-i-1][DATABITS-1-j];
			##1;
		     end
		end

	      ul_in = '0;
	      dl_in = '1;
	      
	      for (int i = 0; i < CMEMSIZE+DMEMSIZE; ++i)
		begin
		   for (int j=0; j < DATABITS; ++j)
		     begin
//			sd_in = wdata[CMEMSIZE+DMEMSIZE-i-1][DATABITS-1-j];
			sd_in = '0;
			rdata = { rdata[DATABITS-2:0], sd_out };
			##1;
		     end
		   T2_read: assert (rdata == wdata[CMEMSIZE+DMEMSIZE-i-1]) 
		     else $error("T2: wrote %b, got %b", wdata[CMEMSIZE+DMEMSIZE-i-1], rdata);
		end
	      
	      sde_in = '0;
	      ul_in = '0;
	      dl_in = '0;	      
	      ##1;
	      
	      //////////////////////////////////////////////////////////////////////////////////////
	      // T3-1 UPLOAD
	      //////////////////////////////////////////////////////////////////////////////////////

	      $info("T3-1: UPLOAD");
	      
	      for (int i = 0; i < CMEMSIZE; ++i)	
		begin
		   if (i < NTAPS)
		     wdata[i] = coeffs[i];
		   else
		     wdata[i] = '0;
		end
	      
	      sde_in = '1;
	      ul_in = '1;
	      ##1;
	      
	      for (int i = 0; i < DMEMSIZE; ++i)
		for (int j=0; j < DATABITS; ++j)
		  begin
		     sd_in = '0;
		     ##1;
		  end
	      
	      for (int i = 0; i < CMEMSIZE; ++i)
		begin
		   for (int j=0; j < DATABITS; ++j)
		     begin
			sd_in = wdata[CMEMSIZE-i-1][DATABITS-1-j];
//			$info("%d-%d", CMEMSIZE-i-1, DATABITS-1-j);		  
			##1;
		     end
		end

	      sde_in = '0;
	      ul_in = '0;
	      ##1;
	      
	      wait (test_done);
	      

	   end : control_inputs

	   
	   begin : data_io

	      //////////////////////////////////////////////////////////////////////////////////////
	      // T3-2 STEP
	      //////////////////////////////////////////////////////////////////////////////////////
	      
	      cb.extready_in <= '1;
	      @(cb iff cb.extvalid_out);
	      $info("T3-2 STEP");	      
	      
	      repeat(NTAPS)
		begin
		   cb.ext_in <= '0;
		   @(cb iff cb.extvalid_out);
		   $display("%8d %24b", cb.ext_out, cb.ext_out);
		end

	      repeat(NTAPS)	      
		begin
		   cb.ext_in <= L;
		   @(cb iff cb.extvalid_out);
		   $display("%8d %24b", cb.ext_out, cb.ext_out);
		end
	      
	      repeat(NTAPS)	      
		begin
		   cb.ext_in <= '0;
		   @(cb iff cb.extvalid_out);
		   $display("%8d %24b", cb.ext_out, cb.ext_out);
		end

	      //////////////////////////////////////////////////////////////////////////////////////
	      // T3-3 IMPULSE
	      //////////////////////////////////////////////////////////////////////////////////////
	      
	      $info("T3-3 IMPULSE");	      

	      repeat(NTAPS)
		begin
		   cb.ext_in <= '0;
		   @(cb iff cb.extvalid_out);
		   $display("%8d %24b", cb.ext_out, cb.ext_out);
		end

	      cb.ext_in <= L;	      
	      @(cb iff cb.extvalid_out);
	      $display("%8d %24b", cb.ext_out, cb.ext_out);
	      
	      repeat(NTAPS)	      
		begin
		   cb.ext_in <= '0;
		   @(cb iff cb.extvalid_out);
		   $display("%8d %24b", cb.ext_out, cb.ext_out);
		end

	      //////////////////////////////////////////////////////////////////////////////////////
	      // T3-3 EXTREADY
	      //////////////////////////////////////////////////////////////////////////////////////
	      
	      $info("T3-4 EXTREADY");	      

	      cb.extready_in <= '1;
	      repeat(NTAPS)
		begin
		   @(cb iff cb.extvalid_out);
		   cb.ext_in <= $urandom;
		   cb.extready_in <= '0;
		   ##10;
		   cb.extready_in <= '1;
		end

	      
	      test_done = '1;
	      
	   end : data_io

	join_any
	
	$finish;
	
     end : test_program

   
   
endprogram


