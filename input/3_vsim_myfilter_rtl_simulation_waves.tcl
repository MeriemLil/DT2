proc analog_wave { path } {
    set obj [find signals $path]
    set obj_value [examine $obj]
    set obj_bits [string range $obj_value 0 [expr [string first "'" $obj_value] - 1]]
    set obj_max [expr (2 ** ($obj_bits-1)) - 1]
    set obj_min [expr -(2 ** ($obj_bits-1))]
    add wave -radix decimal -format Analog-Step -height 84 -max $obj_max -min $obj_min $path
}

onerror {resume}
add wave -noupdate /myfilter_tb/DUT_INSTANCE/clk
add wave -noupdate /myfilter_tb/DUT_INSTANCE/rst_n
add wave -noupdate -divider Ports
add wave -noupdate /myfilter_tb/DUT_INSTANCE/scl_inout
add wave -noupdate /myfilter_tb/DUT_INSTANCE/sda_inout
add wave -noupdate /myfilter_tb/DUT_INSTANCE/extready_in
add wave -noupdate /myfilter_tb/DUT_INSTANCE/ext_in
analog_wave /myfilter_tb/DUT_INSTANCE/ext_in
analog_wave /myfilter_tb/DUT_INSTANCE/extvalid_out
add wave -noupdate /myfilter_tb/DUT_INSTANCE/ext_out
analog_wave /myfilter_tb/TEST/ext_out_sampled

add wave -noupdate -divider Internal

add wave -noupdate /myfilter_tb/DUT_INSTANCE/sde
add wave -noupdate /myfilter_tb/DUT_INSTANCE/sdin
add wave -noupdate /myfilter_tb/DUT_INSTANCE/sdout
add wave -noupdate /myfilter_tb/DUT_INSTANCE/ul
add wave -noupdate /myfilter_tb/DUT_INSTANCE/dl
add wave -noupdate /myfilter_tb/DUT_INSTANCE/srst_n

add wave -noupdate -divider {State Machines}
add wave -noupdate /myfilter_tb/DUT_INSTANCE/filter_unit_1/dpc_1/state_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_fsm_1/state_r

add wave -noupdate -divider {Registers}
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_sync_1/scl_sff1_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_sync_1/scl_sff2_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_sync_1/past_scl_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_sync_1/sda_sff1_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_sync_1/sda_sff2_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_sync_1/past_sda_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_ctr_1/bitctr_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_ctr_1/bytectr_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/i2c_slave_1/i2c_srg_1/srg_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/filter_unit_1/cmem_1/mem_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/filter_unit_1/dmem_1/mem_r
add wave -noupdate /myfilter_tb/DUT_INSTANCE/filter_unit_1/acc_1/acc_r

configure wave -signalnamewidth 1
configure wave -datasetprefix 0
wave zoom full
update

