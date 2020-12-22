`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_sync
  
  (input logic clk,
   input logic rst_n,

   input logic sda_in,   
   input logic scl_in,

   output logic sda_out,
   output logic scl_out,

   output logic past_sda_out,
   output logic past_scl_out
   );

   
   logic scl_sff1_r;
   logic scl_sff2_r;
   logic sda_sff1_r;
   logic sda_sff2_r;
   logic past_scl_r;
   logic past_sda_r;

   always_ff@(posedge clk or negedge rst_n)
     begin: sync_ffs
	if (rst_n == '0)
	 begin
	  scl_sff1_r <= '1;
          scl_sff2_r <= '1;
          sda_sff1_r <= '1;
          sda_sff2_r <= '1;
	 end
	
	else
	 begin
	  scl_sff1_r <= scl_in;
	  sda_sff1_r <= sda_in;
	  scl_sff2_r <= scl_sff1_r;
	  sda_sff2_r <= sda_sff1_r;
	 end
     end


   always_ff@(posedge clk or negedge rst_n)
     begin: edgedet_ffs
	if (rst_n == '0)
	 begin
	  past_sda_r <= '1;
	  past_scl_r <= '1;
	 end

	else
	 begin
	  past_scl_r <= scl_sff2_r;
	  past_sda_r <= sda_sff2_r;
	 end
     end 

   assign scl_out = scl_sff2_r;
   assign past_scl_out = past_scl_r;
   assign past_sda_out = past_sda_r;
   assign sda_out = sda_sff2_r;
   
endmodule


