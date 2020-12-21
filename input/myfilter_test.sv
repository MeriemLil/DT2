`include "myfilter.svh"


`ifndef SYNTHESIS

import myfilter_pkg::*;
import i2c_pkg::*;

program myfilter_test
  
  (input logic clk,
   input logic 		       rst_n,
   i2c_if i2c_bus,
   output logic [DATABITS-1:0] ext_in,
   output logic 	       extready_in,
   input logic [DATABITS-1:0]  ext_out,
   input logic 		       extvalid_out
   );

   localparam real 	       SIMULATION_LENGTH = 10000.0;
   localparam int 	       SAMPLE_PERIOD = 2*NTAPS;
   logic 		       T7_done = '0;
   logic [DATABITS-1:0]        ext_out_sampled = '0;
   

   default clocking cb @(posedge clk);
      output 	#(INPUT_SKEW) ext_in;
      output 	#(INPUT_SKEW) extready_in;   
      input 	ext_out;
      input 	extvalid_out;   
   endclocking
   
   initial
     begin : test_program

	///////////////////////////////////////////////////////////////////////////////
	// Bus master process
	///////////////////////////////////////////////////////////////////////////////
	
	fork
	   begin : bus_master
	      logic ack;
	      logic [7:0] tmp;
	      
	      $info("T1 RESET");	      
	      wait(rst_n);
	      #1us;

	      ////////////////////////////////////////////////////////////////
	      // T2: START FILTER
	      ////////////////////////////////////////////////////////////////

	      // To do: Add test
	      

              // wait(T7_done);

	      ////////////////////////////////////////////////////////////////
	      // T8: STOP FILTER
	      ////////////////////////////////////////////////////////////////

	      $info("T8 STOP");

	      // To do: Add test	      

	      
	      #100us;
	      
	   end : bus_master

	   ///////////////////////////////////////////////////////////////////////////////
	   // ext_in driver process
	   ///////////////////////////////////////////////////////////////////////////////
	   

	   begin : ext_in_driver

	      const real pi = 3.14159265359;
	      real 	 angle;
	      logic signed [DATABITS-4:0] noise;
	      ext_in = '0;
	      
	      //////////////////////////////////////////////////////////////
	      //
	      // T3 Step
	      //
	      //////////////////////////////////////////////////////////////

	      @(cb iff cb.extvalid_out);
	      
	      $info("T3 STEP");
	      
	      cb.ext_in <= '0;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);
	      
	      cb.ext_in <= L;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);

	      cb.ext_in <= '0;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);

	      //////////////////////////////////////////////////////////////
	      //
	      // T4 Negative Step
	      //
	      //////////////////////////////////////////////////////////////

	      @(cb iff cb.extvalid_out)
		$info("T4 NEG STEP");
	      
	      cb.ext_in <= '0;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);
	      
	      cb.ext_in <= -L;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);

	      cb.ext_in <= '0;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);
	      

	      //////////////////////////////////////////////////////////////
	      //
	      // T5 Impulse
	      //
	      //////////////////////////////////////////////////////////////

	      @(cb iff cb.extvalid_out)
		$info("T5 IMPULSE");
	      
	      cb.ext_in <= '0;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);
	      
	      cb.ext_in <= -L;
	      @(cb iff cb.extvalid_out);	      

	      cb.ext_in <= '0;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);
	      
	      
	      //////////////////////////////////////////////////////////////
	      //
	      // T6 Negative Impulse
	      //
	      //////////////////////////////////////////////////////////////

	      @(cb iff cb.extvalid_out)
		$info("T6 NEG IMPULSE");
	      
	      cb.ext_in <= '0;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);
	      
	      cb.ext_in <= -L;
	      @(cb iff cb.extvalid_out);	      

	      cb.ext_in <= '0;
	      repeat(NTAPS) @(cb iff cb.extvalid_out);
	      
	      //////////////////////////////////////////////////////////////
	      //
	      // T7 Frequency Sweep
	      //
	      //////////////////////////////////////////////////////////////
	      
	      @(posedge clk iff extvalid_out == '1)
		$info("T7 SWEEP");
	      
	      forever
		begin
		   angle = 0.0;		
		   for (real sample = 0.0; sample < SIMULATION_LENGTH; sample += 1.0)
		     begin
			@(cb iff cb.extvalid_out);
			  begin
			     ext_in = ((2**(DATABITS-3))-1)*$sin(angle);
			     angle = angle + (sample/SIMULATION_LENGTH)*(pi/2.0);
			  end

		     end
		   T7_done = '1;
		end
	   end : ext_in_driver
	   
	   ///////////////////////////////////////////////////////////////////////////////
	   // ext_out reader process
	   ///////////////////////////////////////////////////////////////////////////////
	   
	   begin : ext_out_reader
	      forever
		begin
		   @(cb iff cb.extvalid_out)
		     ext_out_sampled = cb.ext_out;
		end
	   end : ext_out_reader


	   begin : sampling_clock
	      int tmr;
	      tmr = 0;
	      forever
		begin
		   @(posedge clk);
		   if (extvalid_out == '1)
		     tmr = SAMPLE_PERIOD;
		   if (tmr == 0)
		     cb.extready_in <= '1;
		   else
		     begin
			cb.extready_in <= '0;
			tmr = tmr - 1;
		     end
		end
	   end : sampling_clock
	   
	join_any
	
	$finish;
	
     end : test_program
   
endprogram
   
`endif
