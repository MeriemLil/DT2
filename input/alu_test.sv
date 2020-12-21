`include "myfilter.svh"
import myfilter_pkg::*;

program alu_test  
  (input logic clk,
   input logic 		      rst_n,
   output logic [DATABITS-1:0] m1_in,
   output logic [DATABITS-1:0] m2_in,
   output 		      alu_cmd_t cmd_in, 
   output logic [ACCBITS-1:0]  acc_in,
   input logic [ACCBITS-1:0] d_out
   );

   initial
     begin : test_program
	m1_in = '0;
	m2_in = '0;
	acc_in = '0;
	cmd_in = ALU_NOP;
	
	/////////////////////////////////////////////////////////////////////////////////
	// T1 Select source
	/////////////////////////////////////////////////////////////////////////////////
	
	$info("T1 src select");	

	m1_in = 2;
	m2_in = -3;
	acc_in = 4;

	cmd_in = ALU_NOP;
	@(negedge clk);	
	T1_src_acc: assert($signed(d_out) == $signed(acc_in)) else $error("d_out != acc_in");

	cmd_in = ALU_M1;
	@(negedge clk);	
	T1_src_c: assert($signed(d_out) == $signed(m1_in)) else $error("d_out != m1_in");

	cmd_in = ALU_M2;
	@(negedge clk);	
	T1_src_d: assert($signed(d_out) == $signed(m2_in)) else $error("d_out != m2_in");

	cmd_in = ALU_MU;
	@(negedge clk);	
	T1_src_mul: assert($signed(d_out) == $signed(m1_in) * $signed(m2_in)) else $error("d_out != m1_in * m2_in");

	/////////////////////////////////////////////////////////////////////////////////
	// T2 Complement
	/////////////////////////////////////////////////////////////////////////////////
	
	$info("T2 complement");	
	cmd_in = ALU_ACN;
	@(negedge clk);
	T2_compl: assert($signed(d_out) == -$signed(acc_in)) else $error("d_out != -acc_in");

	/////////////////////////////////////////////////////////////////////////////////
	// T3 Addition
	/////////////////////////////////////////////////////////////////////////////////
	
	$info("T3 add acc+c");	
	cmd_in = ALU_ADM1;
	@(negedge clk);
	T3_add: assert($signed(d_out) == $signed(acc_in) + $signed(m1_in)) else $error("d_out != acc_in + m1_in");
	
	/////////////////////////////////////////////////////////////////////////////////
	// T4 Saturate and Round
	/////////////////////////////////////////////////////////////////////////////////
	
	$info("T4 saturate and round");	
	cmd_in = ALU_SATA;
	acc_in = '1;
	acc_in[$bits(acc_in)-1] = '0;
	@(negedge clk);
	T4_sat_pos: assert(d_out[ACCBITS-1:DATABITS] == 0) else $error("Non-zero bits in MSBs of saturated positive number.");

	cmd_in = ALU_SATA;
	acc_in = '0;
	acc_in[$bits(acc_in)-1] = '1;
	@(negedge clk);
	T4_sat_neg: assert(&(d_out[ACCBITS-1:DATABITS]) == '1) else $error("Zero bits in MSBs of saturated negative number.");

	cmd_in = ALU_SATA;
	acc_in = (2**(DATABITS-1))-1;
	@(negedge clk);
	T4_round_pos: assert($signed(d_out) == 0) else $error("Positive number < 1 not rounded to zero.");

	cmd_in = ALU_SATA;
	acc_in = -(2**(DATABITS-1));
	@(negedge clk);
	T4_round_neg: assert($signed(d_out) == -1) else $error("Negative number > -1 not rounded to -1");

	repeat(100)
	  begin
	     cmd_in = ALU_SATA;
	     std::randomize(acc_in);
	     @(negedge clk);
	  end

	repeat(200)
	  begin
	     cmd_in = ALU_NOP;
	     std::randomize(acc_in);
	     @(negedge clk);
	  end

	repeat(200)
	  begin
	     cmd_in = ALU_SATA;
	     std::randomize(acc_in);
	     @(negedge clk);
	  end
	
	/////////////////////////////////////////////////////////////////////////////////
	// T5 MAXMIN-MAC
	/////////////////////////////////////////////////////////////////////////////////
	
	$info("T5 MAXMIN-MAC");
	acc_in = '0;
	m1_in = 2**(DATABITS-1)-1;
	m2_in = 2**(DATABITS-1)-1;
	cmd_in = ALU_MU;
	repeat(NTAPS)
	  begin
	     @(negedge clk);
	     acc_in = d_out;
	     cmd_in = ALU_ADMU;	     
	  end
	T5_maxmac: assert($signed(d_out) == NTAPS*$signed(m1_in)*$signed(m2_in)) else $error("d_out wrong");
	
	acc_in = '0;
	m1_in = -2**(DATABITS-1);
	m2_in = -2**(DATABITS-1);
	cmd_in = ALU_MU;
	repeat(NTAPS)
	  begin
	     @(negedge clk);
	     acc_in = d_out;
	     cmd_in = ALU_ADMU;	     
	  end
	T5_minmac: assert($signed(d_out) == NTAPS*$signed(m1_in)*$signed(m2_in)) else $error("d_out wrong");

	/////////////////////////////////////////////////////////////////////////////////
	// T6 STEP
	/////////////////////////////////////////////////////////////////////////////////
	
	$info("T6 STEP");
	m2_in = L;
	
	if (NTAPS > 7)
	  begin
	     acc_in = '0;
	     m1_in = K16;
	     cmd_in = ALU_MU;
	     @(negedge clk);
	     acc_in = d_out;
	     m1_in = K8;
	     cmd_in = ALU_ADMU;
	     @(negedge clk);
	     acc_in = d_out;
	     cmd_in = ALU_ADMU;	     
	  end
	else if (NTAPS > 5)
	  begin
	     acc_in = '0;
	     m1_in = K8;
	     cmd_in = ALU_MU;
	     @(negedge clk);
	     acc_in = d_out;
	     cmd_in = ALU_ADMU;
	  end
	else
	  begin
	     acc_in = '0;
	     cmd_in = ALU_MU;
	  end
	
	m1_in = K4;
	@(negedge clk);
	m1_in = K2;	
	acc_in = d_out;
	cmd_in = ALU_ADMU;	     
	@(negedge clk);
	m1_in = K;	
	acc_in = d_out;
	cmd_in = ALU_ADMU;	     
	@(negedge clk);
	m1_in = K2;	
	acc_in = d_out;
	cmd_in = ALU_ADMU;	     
	@(negedge clk);
	m1_in = K4;	
	acc_in = d_out;
	cmd_in = ALU_ADMU;	     
	@(negedge clk);

	if (NTAPS > 7)
	  begin
	     acc_in = d_out;
	     m1_in = K8;
	     cmd_in = ALU_ADMU;
	     @(negedge clk);
	     acc_in = d_out;
	     m1_in = K16;
	     cmd_in = ALU_ADMU;
	     @(negedge clk);
	  end
	else if (NTAPS > 5)
	  begin
	     acc_in = d_out;
	     m1_in = K8;
	     cmd_in = ALU_ADMU;
	     @(negedge clk);
	  end

	acc_in = d_out;
	m1_in = '0;
	m2_in = '0;	
	cmd_in = ALU_SATA;
	@(negedge clk);
	
	$finish;
	
     end : test_program
   
endprogram

   
