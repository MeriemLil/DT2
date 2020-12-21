onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/clk
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/rst_n
add wave -noupdate -divider PORTS
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/scl_inout
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/sda_inout
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/ul_out
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/dl_out
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/sd_out
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/sde_out
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/sd_in
add wave -noupdate -divider {INTERNAL SIGNALS}
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/scl
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/sda
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/past_scl
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/past_sda
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/start
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/stop
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/scl_rise
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/scl_fall
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/byteok
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/frameok
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/next
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/byteen
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/clr
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/oe
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/osel
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/ack
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/lastbit
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/addrok
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/sdaw
add wave -noupdate -divider REGISTERS
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_sync_1/scl_sff1_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_sync_1/scl_sff2_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_sync_1/sda_sff1_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_sync_1/sda_sff2_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_sync_1/past_sda_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_sync_1/past_scl_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_srg_1/srg_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_ctr_1/bitctr_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_ctr_1/bytectr_r
add wave -noupdate /i2c_slave_tb/DUT_INSTANCE/i2c_fsm_1/state_r

configure wave -signalnamewidth 1
configure wave -datasetprefix 0
wave zoom full
update
