`include "myfilter.svh"
///////////////////////////////////////////////////////////////
//
// Template for top-level module
//
///////////////////////////////////////////////////////////////

`ifndef SYNTHESIS

import myfilter_pkg::*;



module myfilter_svamod
  
  (input logic clk,
   input logic 		      rst_n,
   inout tri 		      scl_inout,
   inout tri 		      sda_inout,
   input logic [DATABITS-1:0] ext_in,
   input logic 		      extready_in,
   input logic [DATABITS-1:0] ext_out,
   input logic 		      extvalid_out,
   input logic 		      sde,
   input logic 		      sdin,
   input logic 		      ul,
   input logic 		      dl,   
   input logic 		      sdout, 
   input logic 		      srst_n
   );
   
 `include "i2c_assumes.svh"   

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   X_sda_inout: assert property ( @(posedge clk) disable iff (rst_n !== '1) (sda_inout !== 'x))
     else $error("myfilter port sda_inout in unknown state");
   X_scl_inout: assert property ( @(posedge clk) disable iff (rst_n !== '1) (scl_inout !== 'x))
     else $error("myfilter port scl_inout in unknown state");   
   `xcheck(ext_in);
   `xcheck(extready_in);
   `xcheck(ext_out);
   `xcheck(extvalid_out);
   `xcheck(sde);
   `xcheck(sdin);
   `xcheck(ul);
   `xcheck(dl);   
   `xcheck(sdout); 
   `xcheck(srst_n);

   ///////////////////////////////////////////////////////////////////////////////////////
   // Property Checks
   ///////////////////////////////////////////////////////////////////////////////////////   
	
endmodule


`endif //  `ifndef SYNTHESIS
