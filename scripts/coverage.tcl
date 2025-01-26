# With IVA many scenarious of parallel work of processing blocks can be seen. This helps coverage analysis in a way where interesting scenarious can be seen at lower bound.

# no IVA
# set task_name = <embedded>

# IVA abstraction addded
# set task_name = iva_debug

# Create coverage task and add relevant checkers
task -create coverage -set -source_task iva_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {<embedded>::top.chk_top.*coverage*
	<embedded>::top.subsys.intcon.chk_axi_prot_pb0.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_pb1.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_pp.ast_axi*_r_* 
	<embedded>::top.subsys.intcon.chk_axi_prot_pp.ast_axi*_ar_* 
	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_reg.ast_axi* 
}
cover -remove *


# waive checker cover points
check_cov -waiver -add -instance chk_top -comment {Checker module}
check_cov -waiver -add -instance subsys.packet_builder0.chk_data_integrity -comment {Checker module}
# waive COI unreachable cover points
check_cov -waiver -add -cover_item_id { 1231 1232 1233 1235}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1224 1226 1227 1228 1229 1222 1223}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1225 1230}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 39 40 1335 3778 1300 1338 3780 1302 1416 861 1306 641 789 1345 865 645 3531 3532 1352 1316 3758 3832 2612 1319 3243 323 1803 324 325 2434 3806 1698 3808}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 4165 3351 3759 1772 2435 4329 2581 3244 4486 1699}  -comment {Design is not fully utilized}
# check_cov -measure -max_jobs 5 -task {coverage} -bg

# Waive memories
check_cov -waiver -add -instance inmem  -comment {Design is not fully utilized}
check_cov -waiver -add -instance outmem  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 4508 2588 4187 2442 3258 3365 4351}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 3553 1310 2619 3827 3829 1331 3779 3799 2441 3257 3801 3853 3552}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1515}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1528}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1536}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1560}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1615 1599 1633 1686 1586 1620 1671 1690 1676 1661}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 2329 2363 2414 2279 2433 2419 2404 2303 2271 2358 2342 2376 2258 2429}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 3145 3179 3230 3095 3249 3235 3220 3119 3087 3174 3158 3192 3074 3245}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 3757 3742 3641 3609 3696 3680 3714 3596 3767 3667 3701 3752 3617 3771}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1179 1180 1049 1181 1050 1182 1051 1183 1052 1053 1192 1062 1193 1063 1194 1064 1195 1065 1196 1066 1075 1076 1077 1078 1079 1088 1089 1090 1091 1092 1101 1102 1103 1104 1105 1114 1115 1116 1117 1118 1127 1128 997 1129 998 1130 999 1131 1000 1001 1140 1141 1010 1011 1142 1012 1143 1013 1144 1014 1153 1154 1023 1155 1024 1156 1025 1157 1026 1027 1166 1036 1167 1037 1168 1038 1169 1039 1170 1040}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 4089 4227 4629 4228 4565 4566 4099 4568 4574 4575 4308 4309 4446 4245 4246 4247 4248 4517 4518 4519 4253 4588 4522 4523 4456 4061 4597 4196 4062 4197 4267 4201 4540 1257 4541 1260 1261 4276 4278 1265 4548 1266 4418 4419 4219 4220}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 3387 4237 4560 4136 4493 2353 3169 4076 4433 1850 2666 1274}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1106 1107 1145 1146 1184 1171}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1175 1108 1110 1147 1149 1188}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 2091}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 2092}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 2907}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 2908}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 3432}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 3431}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 3877 3945 4018}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 4133 4274 4242 4073 4282}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 4335 4319 4337 4321 4339 4323 4325 4343 4327 4345 4347 4331 4349 4333}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 4332 4334 4336 4077 4338 4340 4344 4346 4348 4350 4279 4320 4283 4284 4322 4137 4249 4324 4326 4328}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 4557 4490 4644 4650 4430 4364 4385}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 4645 4561 4494 4651 4434}  -comment {Design is not fully utilized}

check_cov -waiver -add -cover_item_id { 1963} -comment {If there is more than one pulse, crc can not be on the last byte in axi beat.}
check_cov -waiver -add -cover_item_id { 2350 1943}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 1944} -comment {It can not occur because it is not the first data beat, data can be only on 0th and 1st byte location.}
check_cov -waiver -add -cover_item_id { 2354 1964}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 3166 2759 2779}  -comment {Design is not fully utilized}
check_cov -waiver -add -cover_item_id { 2760 3170 2780} -comment {Design is not fully utilized}


# Checker COI checked, Proof core not checked

check_cov -waiver -add -cover_item_id { 639 642} -comment {No axi write to inmem}
check_cov -waiver -add -cover_item_id { 863 866} -comment {No axi read to outmem}
check_cov -waiver -add -cover_item_id { 4106} -comment {lsb awaddr field always 0 - word allignment}
check_cov -waiver -add -cover_item_id { 4458 4463 4449 4450 4451} -comment {No axi write to exreg}
check_cov -waiver -add -cover_item_id { 4605} -comment {word allignment} 

check_cov -waiver -add -cover_item_id { 3583} -comment {no axi write in parser}
check_cov -waiver -add -cover_item_id { 4000 4003 4004} -comment {pp_sts_reg never used because this info is provided directly on top level}
check_cov -waiver -add -cover_item_id { 3264 3319 3287 3339 3358 3360 3362 3295 3364} -comment {pkt_type data not used in the system}
check_cov -waiver -add -cover_item_id { 3474 3476 3494 3482} -comment {pulse_cnt_reg not important for parser}
check_cov -waiver -add -cover_item_id { 2614} -comment {checked in pb0}
check_cov -waiver -add -cover_item_id { 3357 3359 3361 3363} -comment {pkt_type data not used in the system}
check_cov -waiver -add -cover_item_id { 3673 3744 3751 3669} -comment {system is never reseted after reset analysis}
