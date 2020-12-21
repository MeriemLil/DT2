`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module alu_svamod  
  (input logic clk,
   input logic 		      rst_n,
   input logic [DATABITS-1:0] m1_in,
   input logic [DATABITS-1:0] m2_in,
   input 		      alu_cmd_t cmd_in, 
   input logic [ACCBITS-1:0]  acc_in,
   input logic [ACCBITS-1:0]  d_out
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   

   `xcheck(m1_in);
   `xcheck(m2_in);
   `xcheck(cmd_in); 
   `xcheck(acc_in);
   `xcheck(d_out);

   property p_ALU_NOP;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_NOP) |-> d_out == acc_in;
   endproperty
   
   a_ALU_NOP: assert property (p_ALU_NOP);

   
   property p_ALU_M1;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_M1) |-> $signed(d_out) == $signed(m1_in) ;
   endproperty
   
   a_ALU_M1: assert property (p_ALU_M1);


   property p_ALU_M2;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_M2) |-> $signed(d_out) == $signed(m2_in) ;
   endproperty
   
   a_ALU_M2: assert property (p_ALU_M2);


   property p_ALU_MU;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_MU) |-> $signed(d_out) == $signed(m1_in) * $signed(m2_in) ;
   endproperty
   
   a_ALU_MU: assert property (p_ALU_MU);


   property p_ALU_ACN;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_ACN) |-> $signed(d_out) ==  -$signed(acc_in) ;
   endproperty
   
   a_ALU_ACN: assert property (p_ALU_ACN);


   property p_ALU_M1N;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_M1N) |-> $signed(d_out) ==  -$signed(m1_in) ;
   endproperty
   
   a_ALU_M1N: assert property (p_ALU_M1N);


   property p_ALU_M2N;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_M2N) |-> $signed(d_out) ==  -$signed(m2_in) ;
   endproperty
   
   a_ALU_M2N: assert property (p_ALU_M2N);


   property p_ALU_MUN;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_MUN) |-> $signed(d_out) ==  -($signed(m1_in) * $signed(m2_in)) ;
   endproperty
   
   a_ALU_MUN: assert property (p_ALU_MUN);


   property p_ALU_ADAC;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_ADAC) |-> $signed(d_out) ==  ($signed(acc_in) + $signed(acc_in)) ;
   endproperty
   
   a_ALU_ADAC: assert property (p_ALU_ADAC);


   property p_ALU_ADM1;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_ADM1) |-> $signed(d_out) ==  ($signed(acc_in) + $signed(m1_in)) ;
   endproperty
   
   a_ALU_ADM1: assert property (p_ALU_ADM1);


   property p_ALU_ADM2;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_ADM2) |->  $signed(d_out) ==  ($signed(acc_in) + $signed(m2_in)) ;
   endproperty
   
   a_ALU_ADM2: assert property (p_ALU_ADM2);


   property p_ALU_ADMU;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_ADMU) |-> $signed(d_out) ==  ($signed(acc_in) + ($signed(m1_in) * $signed(m2_in))) ;
   endproperty
   
   a_ALU_ADMU: assert property (p_ALU_ADMU);


   property p_ALU_SUAC;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_SUAC) |-> $signed(d_out) ==  ($signed(acc_in) - $signed(acc_in)) ;
   endproperty
   
   a_ALU_SUAC: assert property (p_ALU_SUAC);


   property p_ALU_SUM1;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_SUM1) |-> $signed(d_out) ==  ($signed(acc_in) - $signed(m1_in)) ;
   endproperty
   
   a_ALU_SUM1: assert property (p_ALU_SUM1);


   property p_ALU_SUM2;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_SUM2) |-> $signed(d_out) ==  ($signed(acc_in) - $signed(m2_in)) ;
   endproperty
   
   a_ALU_SUM2: assert property (p_ALU_SUM2);


   property p_ALU_SUMU;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_SUMU) |-> $signed(d_out) ==  ($signed(acc_in) - ($signed(m1_in) * $signed(m2_in))) ;
   endproperty
							 
   a_ALU_SUMU: assert property (p_ALU_SUMU);

							 
   property p_ALU_SATA;
      logic 		      satp;							 
      logic 		      satn;
      logic [DATABITS-1:0]    ip;
      logic [(ACCBITS-DATABITS-(DATABITS-1))-1:0] op;
      logic [DATABITS-1:0] 			  psv;
      logic [DATABITS-1:0] 			  nsv;      
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_SATA,
	 ip = acc_in[2*DATABITS-2:DATABITS-1],
	 op = acc_in[ACCBITS-1:2*DATABITS-2],
	 satp = !acc_in[ACCBITS-1] && (| op),
	 satn = acc_in[ACCBITS-1] && !(& op),
	 psv = { 1'b0, {(DATABITS-1) {1'b1}} },
	 nsv = { 1'b1, {(DATABITS-1) {1'b0}} }	 
	 ) |-> $signed(d_out) == $signed(( acc_in[ACCBITS-1] ? (satn ? nsv : ip) : (satp ? psv : ip) ));
   endproperty
   
   a_ALU_SATA: assert property (p_ALU_SATA) else $error("Saturation/rounding error:: %b |-> %b", acc_in, d_out);

   property p_ALU_SATA_range;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_in == ALU_SATA) |-> ( ($signed(d_out) < (2**(DATABITS-1))) && ($signed(d_out) >= -(2**(DATABITS-1))));
   endproperty
   
   a_ALU_SATA_range: assert property (p_ALU_SATA_range) 
     else $error("Saturated value out of range: %d |-> %d", $signed(acc_in), $signed(d_out));
   
endmodule

`endif
