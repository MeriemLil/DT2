`include "myfilter.svh"
import myfilter_pkg::*;

module reset_sync
  
  (input logic clk,
   input logic rst_n,
   output logic srst_n   
   );
   
   logic q1_r;
   logic q2_r;
   
   always_ff@(posedge clk or negedge rst_n)
      begin
	if (rst_n == '0)
	  begin
	    q1_r <= '0;
 	    q2_r <= '0;
          end

	else
	  begin
	    q1_r <= '1;
	    q2_r <= q1_r;
 	  end
      end

   assign srst_n = q2_r;
   
endmodule

