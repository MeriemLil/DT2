`include "myfilter.svh"

interface i2c_if 
  #(parameter realtime I2C_CLOCK_PERIOD = 10000.0ns, // Parameters
    parameter realtime I2C_HOLD_TIME    = 5000.0ns    
    ) 
   (tri1 scl, sda);                                  // Ports
   
   logic scldrv = 'z, sdadrv = 'z;                   // Variables for driving I2C nets

   assign scl = (scldrv === '0 ? '0 : 'z);           // I2C signal encoding
   assign sda = (sdadrv === '0 ? '0 : 'z);

   task automatic start_condition;
      sdadrv = '0;
      scldrv = '1;      
      #(I2C_CLOCK_PERIOD/2);
   endtask

   task automatic stop_condition;
      sdadrv = '0;
      scldrv = '0;   
      #(I2C_CLOCK_PERIOD/2);
      scldrv = '1;   
      #(I2C_CLOCK_PERIOD/2);
      sdadrv = '1;
      #(I2C_CLOCK_PERIOD/2);      
   endtask

   task automatic write_bit( input logic value );
      scldrv = '0;
      #(I2C_HOLD_TIME);
      sdadrv = value;
      #(I2C_CLOCK_PERIOD/2);
      scldrv = '1;
      #(I2C_CLOCK_PERIOD/2);	   
      //sdadrv = '1;
   endtask

   
   task automatic write_byte ( input logic [7:0] value );
      for (int i = 7; i >= 0; i = i - 1)
	begin
	  scldrv = '0;
      	  #(I2C_HOLD_TIME);
      	  sdadrv = value[i];
      	  #(I2C_CLOCK_PERIOD/2);
          scldrv = '1;
          #(I2C_CLOCK_PERIOD/2);
	  //sdadrv = '1;	 
	end 
   endtask
   
   task automatic read_bit (output logic value);
      scldrv = '0;
      #(I2C_HOLD_TIME);
      value = sdadrv;
      #(I2C_CLOCK_PERIOD/2);
      scldrv = '1;
      #(I2C_CLOCK_PERIOD/2);
      //sdadrv = '1;	  
   endtask; 
   

   task automatic read_byte (output logic [7:0] value);
      for (int i = 7; i >= 0; i = i - 1)
	begin
	  scldrv = '0;
      	  #(I2C_HOLD_TIME);
      	  value[i] = sdadrv;
      	  #(I2C_CLOCK_PERIOD/2);
          scldrv = '1;
          #(I2C_CLOCK_PERIOD/2);
	  //sdadrv = 1;	 
	end 
   endtask
   
endinterface
