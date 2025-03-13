#!/bin/csh -f

setenv PROJ_FORMAL_PATH `pwd`
setenv PP_RTL `pwd`/rtl

setenv PATH "${PROJ_FORMAL_PATH}/scripts:${PATH}"
setenv PATH "${PROJ_FORMAL_PATH}/scripts/other:${PATH}"

echo "Configuration Done. Run make command."