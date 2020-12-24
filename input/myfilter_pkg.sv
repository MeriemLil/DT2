`include "myfilter.svh"

package myfilter_pkg;

   ////////////////////////////////////////////////////////////////////////////////
   //
   // 1. DESIGN PARAMETERS
   //    
   ////////////////////////////////////////////////////////////////////////////////

   // 1.1. Design specifications

   localparam int         NTAPS           = 5;  

`ifndef SYNTHESIS
   localparam realtime CLK_PERIOD         = 7.0ns;
`endif
   
   // 1.2. Constants

   localparam logic [6:0] I2C_ADDRESS     = 7'b1111000;   
   localparam int         DATABITS        = 16;   
   localparam int 	  CMEMSIZE        = NTAPS;
   localparam int 	  DMEMSIZE        = NTAPS;   
   localparam int         I2C_DATA_BYTES  = ((DMEMSIZE+CMEMSIZE)*DATABITS)/8;
   localparam int         I2C_FRAME_BYTES = I2C_DATA_BYTES + 1;    

   localparam int 	  MULBITS         = DATABITS*2;                // To do: 
   localparam int 	  ACCBITS         = MULBITS + $clog2(NTAPS-1); // To do: 
   localparam logic [DATABITS-1:0] K      = 16'b0_010001010011011;   // To do:
   localparam logic [DATABITS-1:0] K2     = 16'b1_010111010110010;   // To do:
   localparam logic [DATABITS-1:0] K4     = 16'b0_000100010100110;   // To do:
   localparam logic [DATABITS-1:0] K8     = 16'b1_000101110101100;   // To do:
   localparam logic [DATABITS-1:0] K16    = 16'b0_000001000101001;   // To do:
   localparam logic [DATABITS-1:0] L      = 16'b0011111111100000;   // To do:
   
   ////////////////////////////////////////////////////////////////////////////////
   //
   // 2. TYPE DEFINITIONS
   //    
   ////////////////////////////////////////////////////////////////////////////////

   // 2.1. i2c_fsm state type
   
   typedef enum  logic [2:0] 
		 { IDLE = 3'b000, 
		   HRX = 3'b001, 
		   HACK = 3'b010, 
		   RX = 3'b011, 
		   RACK = 3'b100, 
		   TX = 3'b101, 
		   TACK = 3'b110 } i2c_fsm_t;

   // 2.2. dmem command codes
   
   typedef enum logic [1:0] 
		{
		 DMEM_READ  = 2'b00,
		 DMEM_WRITE = 2'b01,
		 DMEM_SHIFT = 2'b10,
		 DMEM_CLEAR = 2'b11		 
		 } dmem_cmd_t;


   // 2.3. alu command codes
   
   typedef enum logic [4:0] 
		{
		 ALU_NOP   =  5'b00_0_0_0, // acc
		 ALU_M1    =  5'b01_0_0_0, // m1
		 ALU_M2    =  5'b10_0_0_0, // m2		 
		 ALU_MU    =  5'b11_0_0_0, // m1*m2
		 ALU_ACN   =  5'b00_1_0_0, // -acc
		 ALU_M1N   =  5'b01_1_0_0, // -m1
		 ALU_M2N   =  5'b10_1_0_0, // -m2		 
		 ALU_MUN   =  5'b11_1_0_0, // -(m1*m2)
		 ALU_ADAC  =  5'b00_0_0_1, // acc + acc
		 ALU_ADM1  =  5'b01_0_0_1, // acc + m1
		 ALU_ADM2  =  5'b10_0_0_1, // acc + m2
		 ALU_ADMU  =  5'b11_0_0_1, // acc + m1*m2		 
		 ALU_SUAC  =  5'b00_1_0_1, // acc - acc
		 ALU_SUM1  =  5'b01_1_0_1, // acc - m1
		 ALU_SUM2  =  5'b10_1_0_1, // acc - m2
		 ALU_SUMU  =  5'b11_1_0_1, // acc - m1*m2		 
		 ALU_SATA  =  5'b00_0_1_1  // (acc >>> DATABITS) and clip
		 } alu_cmd_t;

   // 2.4. acc command codes

   typedef enum logic [1:0] 
		{
		 ACC_NOP   = 2'b00,
		 ACC_LOAD  = 2'b01,
		 ACC_CLEAR = 2'b10		 
		 } acc_cmd_t;

   // 2.5. dpc states

   typedef enum  logic [4:0] { STOPPED, PROGRAM, EXTIN, TAP0, TAP1, TAP2, TAP3, TAP4, SAT, EXTOUT } dpc_fsm_t;

   // 2.6. dpc command vector type   
   
   typedef struct packed
		  {
		     logic [$clog2(CMEMSIZE)-1:0] cmem_addr; // cmem address 
		     dmem_cmd_t                   dmem_cmd;  // dmem command code
		     logic [$clog2(DMEMSIZE)-1:0] dmem_addr; // dmem address
		     alu_cmd_t                    alu_cmd;   // alu command code
		     acc_cmd_t                    acc_cmd;   // acc command code
		     logic 			  extvalid;  // extvalid_out value
		  } dp_cmd_t;                                  


   localparam int CMDBITS = $bits(dp_cmd_t);    // Number of bis in dpc command vector

   // 2.7. dpc command vectors. To do: Add codes for your micro-operations
 
   const dp_cmd_t CMD_NOP =  '{ 3'b000, DMEM_READ, 3'b000, ALU_NOP, ACC_NOP, '0 };
   const dp_cmd_t CMD_CLR =  '{ 3'b000, DMEM_CLEAR, 3'b000, ALU_NOP, ACC_NOP, '0 };
   const dp_cmd_t CMD_SHIFT =  '{ 3'b000, DMEM_SHIFT, 3'b000, ALU_NOP, ACC_NOP, '0 };
   const dp_cmd_t CMD_SAT_SH =  '{ 3'b000, DMEM_READ, 3'b000, ALU_SATA, ACC_LOAD, '0 };
   const dp_cmd_t CMD_TAP0F =  '{ 3'b000, DMEM_READ, 3'b000, ALU_MU, ACC_LOAD, '0 };
   const dp_cmd_t CMD_TAP1 =  '{ 3'b001, DMEM_READ, 3'b001, ALU_ADMU, ACC_LOAD, '0 };
   const dp_cmd_t CMD_TAP2 =  '{ 3'b010, DMEM_READ, 3'b010, ALU_ADMU, ACC_LOAD, '0 };
   const dp_cmd_t CMD_TAP3 =  '{ 3'b011, DMEM_READ, 3'b011, ALU_ADMU, ACC_LOAD, '0 };
   const dp_cmd_t CMD_TAP4 =  '{ 3'b100, DMEM_READ, 3'b100, ALU_ADMU, ACC_LOAD, '0 };
   const dp_cmd_t CMD_TAP0 =  '{ 3'b000, DMEM_READ, 3'b000, ALU_MU, ACC_LOAD, '1 };
   
      
   ////////////////////////////////////////////////////////////////////////////////
   //
   // 3. VERIFICATION PARAMETERS
   //    
   ////////////////////////////////////////////////////////////////////////////////
   
`ifndef SYNTHESIS

   localparam realtime INPUT_SKEW = CLK_PERIOD/2.0;
   
`endif
   
endpackage
