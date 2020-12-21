`include "myfilter.svh"


package i2c_pkg;

`ifndef SYNTHESIS

   parameter real I2C_CLOCK_PERIOD = 2000.0;         
   
   task automatic i2c_start_condition
     (ref logic scl,
      ref logic sda);
            
      sda = '0;
      scl = 'z;      
      #(I2C_CLOCK_PERIOD/2);
            
   endtask


   task automatic i2c_stop_condition
     (ref logic scl,
      ref logic sda);

      sda = '0;
      scl = '0;   
      #(I2C_CLOCK_PERIOD/2);
      scl = 'z;   
      #(I2C_CLOCK_PERIOD/2);
      sda = 'z;
      #(I2C_CLOCK_PERIOD/2);
      
   endtask

   task automatic i2c_write_bit
     ( ref logic scl,
       ref logic sda,
       input logic value
       );

      scl = '0;
      #250ns;
      sda = (value == '1 ? 'z : '0);
      #(I2C_CLOCK_PERIOD/2);
      scl = 'z;
      #(I2C_CLOCK_PERIOD/2);	   

   endtask
   
   task automatic i2c_write_byte
     ( ref logic scl,
       ref logic sda,
       input logic [7:0] value
       );
`pragma protect begin               

      for (int i=7; i >= 0; --i)
	begin
	   scl = '0;
	   #250ns;
	   sda = (value[i] == '1 ? 'z : '0);
	   #(I2C_CLOCK_PERIOD/2);
	   scl = 'z;
	   #(I2C_CLOCK_PERIOD/2);	   
	end
   sda = 'z;

`pragma protect end
   endtask

   task automatic i2c_read_byte
     (ref logic scl,
      ref logic sda,      
      ref logic [7:0] value);
`pragma protect begin               

      for (int i=7; i >= 0; --i)
	begin
	   scl = '0;
	   #(I2C_CLOCK_PERIOD/2);
	   scl = 'z;
	   if (sda === '0)
	     value[i] = '0;
	   else if (sda === 'z)
	     value[i] = '1;
	   else
	     value[i] = sda;  
	   #(I2C_CLOCK_PERIOD/2);
	end
`pragma protect end
   endtask
   

   task automatic i2c_read_ack
     (ref logic scl,
      ref logic sda,
      ref logic ack);

      scl = '0;
      #(I2C_CLOCK_PERIOD/2);
      scl = 'z;   
      ack = sda;
      #(I2C_CLOCK_PERIOD/2);
   endtask; 

   task automatic i2c_write_ack
     (ref logic scl,
      ref logic sda,
      input logic ack);

      scl = '0;
      #250ns;
      sda = (ack ? 'z : '0);
      #(I2C_CLOCK_PERIOD/2);
      scl = 'z;   
      #(I2C_CLOCK_PERIOD/2);
      sda = 'z;
      
   endtask
   
   task automatic random_delay();
      realtime delay;
      delay = real'($urandom_range(1, 100000))/10.0;
      #(delay);
   endtask 

`endif
   
endpackage
   
