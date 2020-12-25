`include "myfilter.svh"
import myfilter_pkg::*;

module alu  
  (input logic clk,
   input logic 		      rst_n,
   input logic [DATABITS-1:0] m1_in,
   input logic [DATABITS-1:0] m2_in,
   input 		      alu_cmd_t cmd_in, 
   input logic [ACCBITS-1:0]  acc_in,
   output logic [ACCBITS-1:0] d_out
   );

   logic signed [DATABITS-1:0] m1;
   logic signed [DATABITS-1:0] m2;
   logic signed [ACCBITS-1:0] acc;
   logic signed [ACCBITS-1:0] d;
   logic [4:0] cmd;


   always_comb
      begin
	m1 = $signed(m1_in);
	m2 = $signed(m2_in);
	acc = $signed(acc_in);

	cmd = cmd_in;
	
	d = '0;

	case (cmd)
          ALU_NOP: d = acc;
	  ALU_M1: d = m1;
	  ALU_M2: d = m2;
	  ALU_MU: d = m1*m2;
	  ALU_ACN: d = -acc;
	  ALU_M1N: d = -m1;
	  ALU_M2N: d = -m2;
	  ALU_MUN: d = -(m1*m2);
	  ALU_ADAC: d = acc + acc;
	  ALU_ADM1: d = acc + m1;
	  ALU_ADM2: d = acc + m2;
	  ALU_ADMU: d = acc + m1*m2;
	  ALU_SUAC: d = acc - acc;
	  ALU_SUM1: d = acc - m1;
	  ALU_SUM2: d = acc - m2;
	  ALU_SUMU: d = acc - m1*m2;
	  ALU_SATA: 
	    begin
	      d = acc >>> (DATABITS - 1);
	      if (d >= 2**(DATABITS-1))
	   	d = 2**(DATABITS-1) - 1;
	      else if (d < -(2**(DATABITS-1)))
	        d = -(2**(DATABITS-1));
	      else
 	   	d = d;
	    end
	endcase

        

      end
   assign d_out = $unsigned(d);
endmodule

   
