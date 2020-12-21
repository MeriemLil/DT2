`include "myfilter.svh"

// bind statements for instantiationg SVA modules

// This macro is defined in myfilter.svh:
`ifdef INCLUDE_ASSERTIONS

`ifdef design_top_is_myfilter
bind myfilter myfilter_svamod SVA_myfilter (.*);
bind i2c_ctr i2c_ctr_svamod SVA_i2c_ctr (.*);
bind i2c_detector i2c_detector_svamod SVA_i2c_detector (.*);
bind i2c_omux i2c_omux_svamod SVA_i2c_omux (.*);
bind i2c_slave i2c_slave_svamod SVA_i2c_slave (.*);
bind i2c_srg i2c_srg_svamod SVA_i2c_srg (.*);
bind i2c_sync i2c_sync_svamod SVA_i2c_sync (.*);
bind cmem cmem_svamod SVA_cmem (.*);
bind dmem dmem_svamod SVA_dmem (.*);
bind alu alu_svamod SVA_alu (.*);
bind acc acc_svamod SVA_acc (.*);
bind dpc dpc_svamod SVA_dpc (.*);
bind filter_unit filter_unit_svamod SVA_acc (.*);
`endif


`ifdef design_top_is_i2c_slave
bind i2c_ctr i2c_ctr_svamod SVA_i2c_ctr (.*);
bind i2c_detector i2c_detector_svamod SVA_i2c_detector (.*);
bind i2c_fsm i2c_fsm_svamod SVA_i2c_fsm (.*);
bind i2c_omux i2c_omux_svamod SVA_i2c_omux (.*);
bind i2c_srg i2c_srg_svamod SVA_i2c_srg (.*);
bind i2c_sync i2c_sync_svamod SVA_i2c_sync (.*);
bind i2c_slave i2c_slave_svamod SVA_i2c_slave (.*);
`endif

`ifdef design_top_is_i2c_detector
bind i2c_detector i2c_detector_svamod SVA_i2c_detector (.*);
`endif

`ifdef design_top_is_i2c_sync
bind i2c_sync i2c_sync_svamod SVA_i2c_sync (.*);
`endif

`ifdef design_top_is_i2c_ctr
bind i2c_ctr i2c_ctr_svamod SVA_i2c_ctr (.*);
`endif

`ifdef design_top_is_i2c_srg
bind i2c_srg i2c_srg_svamod SVA_i2c_srg (.*);
`endif

`ifdef design_top_is_i2c_fsm
bind i2c_fsm i2c_fsm_svamod SVA_i2c_fsm (.*);
`endif

`ifdef design_top_is_i2c_omux
bind i2c_omux i2c_omux_svamod SVA_i2c_omux (.*);
`endif

`ifdef design_top_is_cmem
bind cmem cmem_svamod SVA_cmem (.*);
`endif

`ifdef design_top_is_dmem
bind dmem dmem_svamod SVA_dmem (.*);
`endif

`ifdef design_top_is_alu
bind alu alu_svamod SVA_alu (.*);
`endif

`ifdef design_top_is_acc
bind acc acc_svamod SVA_acc (.*);
`endif

`ifdef design_top_is_dpc
bind dpc dpc_svamod SVA_dpc (.*);
`endif

`ifdef design_top_is_filter_unit
bind cmem cmem_svamod SVA_cmem (.*);
bind dmem dmem_svamod SVA_dmem (.*);
bind alu alu_svamod SVA_alu (.*);
bind acc acc_svamod SVA_acc (.*);
bind dpc dpc_svamod SVA_dpc (.*);
bind filter_unit filter_unit_svamod SVA_acc (.*);
`endif

`endif
