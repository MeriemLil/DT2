`include "myfilter.svh"


import myfilter_pkg::*;

module i2c_slave
  
  (input logic clk,
   input logic 	rst_n,
   inout tri 	scl_inout,
   inout tri 	sda_inout,
   output logic sde_out,
   output logic ul_out,
   output logic dl_out,
   input logic 	sd_in, 
   output logic sd_out
   );

   // i2c_sync
   logic 	sda_sff1_r;
   logic 	sda_sff2_r;
   logic 	scl_sff1_r;
   logic 	scl_sff2_r;   
   logic 	past_sda_r;
   logic 	past_scl_r;
   logic 	scl;
   logic 	sda;
   logic 	past_scl;
   logic 	past_sda;
   
   // i2c_detector   
   logic 	start;
   logic 	stop;
   logic 	scl_rise;
   logic 	scl_fall;
   
   // i2c_fsm
   enum  logic [2:0] { IDLE = 3'b000, HRX = 3'b001, HACK = 3'b010, RX = 3'b011, RACK = 3'b100, TX = 3'b101, TACK = 3'b110 } state_r, next_state;   
   
   logic next;
   logic clr;
   logic oe;
   logic osel;   
   logic ack;
   logic byteen;
   
   // i2c_ctr
   logic [3:0] bitctr_r;
   logic [$clog2(I2C_FRAME_BYTES)-1:0] bytectr_r;
   logic 			       seven;
   logic 			       byteok;
   logic 			       frameok;
	  
   // i2c_srg
   logic [7:0] srg_r;
   logic       addrok;
   logic       lastbit;

   // i2c_wmux
   logic       sdaw;
   
   always_ff @(posedge clk or negedge rst_n)
     begin : i2c_slave_regs
	if (rst_n == '0)
	  begin
	     sda_sff1_r <= '1;
	     sda_sff2_r <= '1;
	     scl_sff1_r <= '1;
	     scl_sff2_r <= '1;
	     past_sda_r <= '1;
	     past_scl_r <= '1;
	     state_r <= IDLE;	 
	     bitctr_r <= '0;
	     bytectr_r <= '0;
	     srg_r <= '0;
	  end
	else
	  begin
	     
	     // i2c_sync/sync_ffs
	     sda_sff1_r <= sda_inout;
	     sda_sff2_r <= sda_sff1_r;
	     scl_sff1_r <= scl_inout;
	     scl_sff2_r <= scl_sff1_r;
	     past_sda_r <= sda_sff2_r;
	     past_scl_r <= scl_sff2_r;
	     
	     // i2c_fsm/i2c_fsm_reg
	     state_r <= next_state;
	     
	     // i2c_ctr/ctr_proc
	     if (clr)
	       begin
		  bitctr_r <= '0;		  
	       end
	     else if (next)
	       begin
		  if (bitctr_r == 8)
		    bitctr_r <= 0;
		  else
		    bitctr_r <= bitctr_r + 1;
	       end

	     if (!byteen)
	       begin
		  bytectr_r <= '0;
	       end
	     else if (next && seven)
	       begin
		  bytectr_r <= bytectr_r + 1;
	       end
	     
	     // i2c_srg/srg_proc	     
	     if (clr)
	       srg_r <= '0;
	     else if (next)
	       srg_r <= { srg_r[$bits(srg_r)-2:0] , sda_sff2_r };

	  end
     end :  i2c_slave_regs

   assign scl = scl_sff2_r;
   assign sda = sda_sff2_r;   
   assign past_scl = past_scl_r;
   assign past_sda = past_sda_r;   
   
   always_comb 
     begin : i2c_slave_logic

	// detector_logic	     

	if (scl_sff2_r == '1 && past_sda_r == '1 && sda_sff2_r == '0)
	  start = '1;
	else
	  start = 0;

	if (scl_sff2_r == '1 && past_sda_r == '0 && sda_sff2_r == '1)
	  stop = '1;
	else
	  stop = 0;

	if (scl_sff2_r == '1 && past_scl_r == '0)
	  scl_rise = '1;
	else
	  scl_rise = '0;

	if (scl_sff2_r == '0 && past_scl_r == '1)
	  scl_fall = '1;
	else
	  scl_fall = '0;

	// bitctr_decode
	
	if (bitctr_r == 8)
	  byteok = '1;
	else
	  byteok = '0;

	if (bitctr_r == 7)
	  seven = '1;
	else
	  seven = '0;

	// bytectr_decode

	if (bytectr_r == I2C_DATA_BYTES)
	  frameok = '1;
	else
	  frameok = '0;
	
	// i2c_srg

	if (srg_r[7:1] == I2C_ADDRESS)
	  addrok = '1;
	else
	  addrok = '0;
	lastbit = srg_r[0];

	// i2c_omux

	if (oe)
	  begin
	     if (osel)
	       sdaw = (sd_in ? 'z : '0);
	     else
	       sdaw = (ack ? 'z : '0);	    
	  end
	else
	  sdaw = 'z;
	
	// i2c_fsm/i2c_fsm_logic

	sde_out = '0;
	ul_out = '0;
	dl_out = '0;
	next = '0;
	clr = '0;
	ack = '0;
	oe = '0;
	osel = '0;		
	byteen = '0;
	next_state = state_r;
	
	case (state_r)
	  IDLE:
	    begin
	       clr = '1;
	       if (start == '1)
		 next_state = HRX;
	       else
		 next_state = IDLE;		 
	    end
	  
	  HRX:
	    begin
	       if (stop)
		 next_state = IDLE;
	       else 
		 begin
		    if (scl_rise)
		      next = '1;
		    if (byteok && scl_fall)
		      next_state = HACK;
		    else
		      next_state = HRX;		      
		 end
	    end
	  
	  HACK:
	    begin
	       
	       if (stop)
		 begin
		    next_state = IDLE;		    
		 end
	       else
		 begin
		    if (addrok)			 
		      begin
			 oe = '1;
			 ack = '0;
			 if (scl_fall)
			   begin
			      clr = '1;
			      if (lastbit)
				next_state = TX;
			      else
				next_state = RX;			      
			   end
			 else
			   begin
			      clr = '0;
			      next_state = HACK;			      				   
			   end
		      end
		    else
		      begin
			 ack = '1;
			 oe = '0;
			 clr = '0;
			 next_state = IDLE;
		      end
		 end
	    end

	  RX:
	    begin
	       byteen = '1;
	       if (stop)
		 next_state = IDLE;		    
	       else
		 begin
		    if (scl_rise)
		      begin
			 next = '1;
		      end
		    if (scl_fall)
		      begin
			 sde_out = '1;
		      end
		    if (byteok && scl_fall)
		      next_state = RACK;
		    else
		      next_state = RX;		      
		 end
	    end
	  
	  RACK:
	    begin
	       byteen = '1;
	       clr = '1;
	       oe = '1;
	       ack = '0;
	       osel = '0;
	       
	       if (stop)
		 begin
		    next_state = IDLE;		    
		 end
	       else
		 begin
		    if (scl_fall)
		      begin
			 if (frameok)
			   next_state = IDLE;
			 else
			   next_state = RX;			   
		      end
		    else
		      next_state = RACK;		    		      
		 end
	    end 
	  
	  TX:
	    begin
	       byteen = '1;
	       oe = '1;
	       ack = '0;
	       osel = '1;
	       
	       if (stop)
		 next_state = IDLE;		    
	       else
		 begin
		    if (scl_rise)
		      begin
			 next = '1;
		      end
		    if (scl_fall)
		      begin
			 sde_out = '1;
		      end
		    if (byteok == '1 && scl_fall)
		      next_state = TACK;
		    else
		      next_state = TX;		      
		 end
	       
	    end
	  
	  TACK:
	    begin
	       byteen = '1;
	       clr = '1;
	       oe = '0;
	       ack = '0;
	       osel = '0;
	       if (stop)
		 begin
		    next_state = IDLE;		    
		 end
	       else
		 begin
		    if (scl_fall)
		      begin
			 if (frameok)
			   next_state = IDLE;
			 else
			   next_state = TX;
		      end
		    else
		      next_state = TACK;		    		      
		 end
	    end
	  
	endcase
	
     end : i2c_slave_logic

   assign sda_inout = sdaw;
   assign sd_out = lastbit;
   
endmodule // i2c_slave


