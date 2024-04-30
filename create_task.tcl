
set task_name cont_stopat_debug_pb0
# set source_task <embedded>

task -create $task_name -set -source_task cont_stopat_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
cont_stopat_debug::top.chk_top.ast_pb0_di 
}
