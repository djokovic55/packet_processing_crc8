
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
check_cov -waiver -add -instance subsys.packet_builder0.chk_data_integrity -comment {Added by GUI, apply waiver on instance 'subsys.packet_builder0.chk_data_integrity'}
# waive COI unreachable cover points
check_cov -waiver -add -cover_item_id { 1231 1232 1233 1235} -comment {Added by GUI, apply waiver on ' 1231 1232 1233 1235'}
check_cov -waiver -add -cover_item_id { 1224 1226 1227 1228 1229 1222 1223} -comment {Added by GUI, apply waiver on ' 1224 1226 1227 1228 1229 1222 1223'}
check_cov -waiver -add -cover_item_id { 1225 1230} -comment {Added by GUI, apply waiver on ' 1225 1230'}
check_cov -waiver -add -cover_item_id { 39 40 1335 3778 1300 1338 3780 1302 1416 861 1306 641 789 1345 865 645 3531 3532 1352 1316 3758 3832 2612 1319 3243 323 1803 324 325 2434 3806 1698 3808} -comment {Added by GUI, apply waiver on ' 39 40 1335 3778 1300 1338 3780 1302 1416 861 1306 641 789 1345 865 645 3531 3532 1352 1316 3758 3832 2612 1319 3243 323 1803 324 325 2434 3806 1698 3808'}
check_cov -waiver -add -cover_item_id { 4165 3351 3759 1772 2435 4329 2581 3244 4486 1699} -comment {Added by GUI, apply waiver on ' 4165 3351 3759 1772 2435 4329 2581 3244 4486 1699'}
# check_cov -measure -max_jobs 5 -task {coverage} -bg
# Waive memories
# check_cov -waiver -add -instance inmem -comment {Added by GUI, apply waiver on instance 'inmem'}
# check_cov -waiver -add -instance outmem -comment {Added by GUI, apply waiver on instance 'outmem'}


check_cov -waiver -add -instance inmem -comment {Added by GUI, apply waiver on instance 'inmem'}
check_cov -waiver -add -instance outmem -comment {Added by GUI, apply waiver on instance 'outmem'}
check_cov -waiver -add -cover_item_id { 4508 2588 4187 2442 3258 3365 4351} -comment {Added by GUI, apply waiver on ' 4508 2588 4187 2442 3258 3365 4351'}
check_cov -waiver -add -cover_item_id { 3553 1310 2619 3827 3829 1331 3779 3799 2441 3257 3801 3853 3552} -comment {Added by GUI, apply waiver on ' 3553 1310 2619 3827 3829 1331 3779 3799 2441 3257 3801 3853 3552'}
check_cov -waiver -add -cover_item_id { 1515} -comment {Added by GUI, apply waiver on ' 1515'}
check_cov -waiver -add -cover_item_id { 1528} -comment {Added by GUI, apply waiver on ' 1528'}
check_cov -waiver -add -cover_item_id { 1536} -comment {Added by GUI, apply waiver on ' 1536'}
check_cov -waiver -add -cover_item_id { 1560} -comment {Added by GUI, apply waiver on ' 1560'}
check_cov -waiver -add -cover_item_id { 1615 1599 1633 1686 1586 1620 1671 1690 1676 1661} -comment {Added by GUI, apply waiver on ' 1615 1599 1633 1686 1586 1620 1671 1690 1676 1661'}
check_cov -waiver -add -cover_item_id { 2329 2363 2414 2279 2433 2419 2404 2303 2271 2358 2342 2376 2258 2429} -comment {Added by GUI, apply waiver on ' 2329 2363 2414 2279 2433 2419 2404 2303 2271 2358 2342 2376 2258 2429'}
check_cov -waiver -add -cover_item_id { 3145 3179 3230 3095 3249 3235 3220 3119 3087 3174 3158 3192 3074 3245} -comment {Added by GUI, apply waiver on ' 3145 3179 3230 3095 3249 3235 3220 3119 3087 3174 3158 3192 3074 3245'}
check_cov -waiver -add -cover_item_id { 3757 3742 3641 3609 3696 3680 3714 3596 3767 3667 3701 3752 3617 3771} -comment {Added by GUI, apply waiver on ' 3757 3742 3641 3609 3696 3680 3714 3596 3767 3667 3701 3752 3617 3771'}
check_cov -waiver -add -cover_item_id { 1179 1180 1049 1181 1050 1182 1051 1183 1052 1053 1192 1062 1193 1063 1194 1064 1195 1065 1196 1066 1075 1076 1077 1078 1079 1088 1089 1090 1091 1092 1101 1102 1103 1104 1105 1114 1115 1116 1117 1118 1127 1128 997 1129 998 1130 999 1131 1000 1001 1140 1141 1010 1011 1142 1012 1143 1013 1144 1014 1153 1154 1023 1155 1024 1156 1025 1157 1026 1027 1166 1036 1167 1037 1168 1038 1169 1039 1170 1040} -comment {Added by GUI, apply waiver on ' 1179 1180 1049 1181 1050 1182 1051 1183 1052 1053 1192 1062 1193 1063 1194 1064 1195 1065 1196 1066 1075 1076 1077 1078 1079 1088 1089 1090 1091 1092 1101 1102 1103 1104 1105 1114 1115 1116 1117 1118 1127 1128 997 1129 998 1130 999 1131 1000 1001 1140 1141 1010 1011 1142 1012 1143 1013 1144 1014 1153 1154 1023 1155 1024 1156 1025 1157 1026 1027 1166 1036 1167 1037 1168 1038 1169 1039 1170 1040'}
check_cov -waiver -add -cover_item_id { 4089 4227 4629 4228 4565 4566 4099 4568 4574 4575 4308 4309 4446 4245 4246 4247 4248 4517 4518 4519 4253 4588 4522 4523 4456 4061 4597 4196 4062 4197 4267 4201 4540 1257 4541 1260 1261 4276 4278 1265 4548 1266 4418 4419 4219 4220} -comment {Added by GUI, apply waiver on ' 4089 4227 4629 4228 4565 4566 4099 4568 4574 4575 4308 4309 4446 4245 4246 4247 4248 4517 4518 4519 4253 4588 4522 4523 4456 4061 4597 4196 4062 4197 4267 4201 4540 1257 4541 1260 1261 4276 4278 1265 4548 1266 4418 4419 4219 4220'}
check_cov -waiver -add -cover_item_id { 3387 4237 4560 4136 4493 2353 3169 4076 4433 1850 2666 1274} -comment {Added by GUI, apply waiver on ' 3387 4237 4560 4136 4493 2353 3169 4076 4433 1850 2666 1274'}
check_cov -waiver -add -cover_item_id { 1106 1107 1145 1146 1184 1171} -comment {Added by GUI, apply waiver on ' 1106 1107 1145 1146 1184 1171'}
check_cov -waiver -add -cover_item_id { 1175 1108 1110 1147 1149 1188} -comment {Added by GUI, apply waiver on ' 1175 1108 1110 1147 1149 1188'}
check_cov -waiver -add -cover_item_id { 2091} -comment {Added by GUI, apply waiver on ' 2091'}
check_cov -waiver -add -cover_item_id { 2092} -comment {Added by GUI, apply waiver on ' 2092'}
check_cov -waiver -add -cover_item_id { 2907} -comment {Added by GUI, apply waiver on ' 2907'}
check_cov -waiver -add -cover_item_id { 2908} -comment {Added by GUI, apply waiver on ' 2908'}
check_cov -waiver -add -cover_item_id { 3432} -comment {Added by GUI, apply waiver on ' 3432'}
check_cov -waiver -add -cover_item_id { 3431} -comment {Added by GUI, apply waiver on ' 3431'}
check_cov -waiver -add -cover_item_id { 3877 3945 4018} -comment {Added by GUI, apply waiver on ' 3877 3945 4018'}
check_cov -waiver -add -cover_item_id { 4133 4274 4242 4073 4282} -comment {Added by GUI, apply waiver on ' 4133 4274 4242 4073 4282'}
check_cov -waiver -add -cover_item_id { 4335 4319 4337 4321 4339 4323 4325 4343 4327 4345 4347 4331 4349 4333} -comment {Added by GUI, apply waiver on ' 4335 4319 4337 4321 4339 4323 4325 4343 4327 4345 4347 4331 4349 4333'}
check_cov -waiver -add -cover_item_id { 4332 4334 4336 4077 4338 4340 4344 4346 4348 4350 4279 4320 4283 4284 4322 4137 4249 4324 4326 4328} -comment {Added by GUI, apply waiver on ' 4332 4334 4336 4077 4338 4340 4344 4346 4348 4350 4279 4320 4283 4284 4322 4137 4249 4324 4326 4328'}
check_cov -waiver -add -cover_item_id { 4557 4490 4644 4650 4430 4364 4385} -comment {Added by GUI, apply waiver on ' 4557 4490 4644 4650 4430 4364 4385'}
check_cov -waiver -add -cover_item_id { 4645 4561 4494 4651 4434} -comment {Added by GUI, apply waiver on ' 4645 4561 4494 4651 4434'}

	# <embedded>::top.subsys.intcon.chk_axi_prot_pb1.ast_axi* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_p0.ast_axi* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_pbp.ast_axi*_r_* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_pp.ast_axi*_ar_* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_reg.ast_axi* 