# Script description

## Main script
- do_top.tcl 
    - Project build, rtl and verif files compilation.
    - Is run with make command
    - Run from here in tcl terminal following precedure calls.
### Abstractions
- abstractions.tcl
    - IVA for Internal Registers
        - **Call:** *registers_iva_abs_proc*
    - IVA Incomming Memory
        - **Call:** *blackbox_controller_abs_proc*
    - Cutout controller interaction with Internal Registers (Controller blackbox)
        - **Call:** *inmem_iva_abs_proc*
    - Disable Packet Builder 1 (Assume always busy)
        - **Call:** *disable_pb1_abs_proc*
### Coverage analysis
- coverage.tcl 
    - **Call:** *run_coverage_proc*
### SST analysis
- ./sst/sst_pb0_di.tcl 
    - Run SST analysis for data integrity property (Packet builder 0).
    - Used for development of new helper properites
    - **Call:** *run_sst_pb0_proc*
- ./sst/ps_pb0_di.tcl
    - Run JasperGold's Proof structure feature
    - Tree-like structure with Assume-Guarantee nodes
    - Used to easily represent target-helper relationship 
    - **Call:** *run_proof_structure_proc*