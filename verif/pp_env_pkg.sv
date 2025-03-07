
package pp_env_pkg;

    typedef enum {IDLE_DI, CHOOSE_BYTE_DI, CRC_CALC_DI, RECEIVE_BYTE_DI, COMPARE_CRC_DI} di_State;
    localparam TEST = 2; 

endpackage