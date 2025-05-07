// Lean compiler output
// Module: Lean.Language.Basic
// Imports: Init.System.Promise Lean.Parser.Types Lean.Util.Trace
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Language_printMessageEndPos;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Language_instInhabitedDynamicSnapshot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object*);
lean_object* l_Lean_Message_toJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1188_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTree;
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_strict_or(uint8_t, uint8_t);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree;
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*);
lean_object* l_IO_CancelToken_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_896_;
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at___Lean_Environment_displayStats_spec__2(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_IO_print___at___IO_println___at___Lean_Environment_displayStats_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_667_;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instTypeNameSnapshotTree;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_desc___autoParam;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instTypeNameSnapshotLeaf;
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = l_Array_empty(lean_box(0));
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set_usize(x_6, 4, x_5);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_Diagnostics_empty() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageLog_empty;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("proj", 4, 4);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = lean_mk_string_unchecked("declName", 8, 8);
x_20 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_19);
x_21 = lean_mk_string_unchecked("decl_name%", 10, 10);
x_22 = l_Lean_mkAtom(x_21);
lean_inc(x_7);
x_23 = lean_array_push(x_7, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_mk_string_unchecked(".", 1, 1);
x_27 = l_Lean_mkAtom(x_26);
x_28 = lean_array_push(x_25, x_27);
x_29 = lean_mk_string_unchecked("toString", 8, 8);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_string_utf8_byte_size(x_29);
lean_inc(x_29);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = l_Lean_Name_mkStr1(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_array_push(x_28, x_35);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_18);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_array_push(x_15, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_13);
lean_ctor_set(x_39, 2, x_38);
lean_inc(x_7);
x_40 = lean_array_push(x_7, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_11);
lean_ctor_set(x_41, 2, x_40);
lean_inc(x_7);
x_42 = lean_array_push(x_7, x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_array_push(x_7, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 2, x_44);
return x_45;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = l_Array_empty(lean_box(0));
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set_usize(x_7, 4, x_6);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_uint64_of_nat(x_5);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set_usize(x_15, 4, x_6);
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_13);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_19);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Syntax_getRange_x3f(x_3, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_SnapshotTask_defaultReportingRange_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_task_pure(x_1);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_instInhabitedSnapshotTask___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_io_as_task(x_4, x_6, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Language_SnapshotTask_ofIO___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_task_pure(x_2);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTask_finished___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_task_map(x_2, x_7, x_8, x_5);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Language_SnapshotTask_map___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Language_SnapshotTask_map___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_Language_SnapshotTask_map(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_io_bind_task(x_9, x_8, x_10, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_5);
lean_ctor_set(x_17, 3, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Language_SnapshotTask_bindIO___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Language_SnapshotTask_bindIO___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l_Lean_Language_SnapshotTask_bindIO(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_task_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SnapshotTask_get___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_io_get_task_state(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_task_get_own(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_task_get_own(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTask_get_x3f___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = l_Array_empty(lean_box(0));
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set_usize(x_7, 4, x_6);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_uint64_of_nat(x_5);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
lean_inc(x_2);
x_15 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set_usize(x_15, 4, x_6);
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_13);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
static lean_object* _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_667_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Language", 8, 8);
x_3 = lean_mk_string_unchecked("SnapshotTree", 12, 12);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instTypeNameSnapshotTree() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_667_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instToSnapshotTreeSnapshotTree() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = l_Array_empty(lean_box(0));
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set_usize(x_9, 4, x_8);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_box(0);
x_14 = lean_uint64_of_nat(x_7);
lean_inc(x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
lean_inc(x_4);
x_16 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_6);
lean_ctor_set_usize(x_16, 4, x_8);
x_17 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint64(x_17, sizeof(void*)*1, x_14);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_apply_1(x_1, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_instToSnapshotTreeOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTask_cancelRec___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_box(0);
x_11 = lean_nat_dec_lt(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_usize_of_nat(x_8);
x_16 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_17 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_3, x_7, x_15, x_16, x_10);
x_18 = lean_apply_1(x_17, x_5);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; 
x_4 = l_instMonadEIO(lean_box(0));
x_5 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed), 1, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1), 5, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
x_8 = x_3;
goto block_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_IO_CancelToken_set(x_16, x_3);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_8 = x_18;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = l_BaseIO_chainTask(lean_box(0), x_9, x_7, x_10, x_12, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTask_cancelRec___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_896_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Language", 8, 8);
x_3 = lean_mk_string_unchecked("SnapshotLeaf", 12, 12);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instTypeNameSnapshotLeaf() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_896_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instToSnapshotTreeSnapshotLeaf() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instToSnapshotTreeDynamicSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_mk_thunk(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_DynamicSnapshot_toTyped_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Language_instInhabitedDynamicSnapshot___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instInhabitedDynamicSnapshot___lam__0___boxed), 1, 0);
x_2 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_896_;
x_3 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0), 1, 0);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Language", 8, 8);
x_6 = lean_mk_string_unchecked("instInhabitedDynamicSnapshot", 28, 28);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Name_toString(x_7, x_9, x_1);
x_11 = l_Lean_Language_Snapshot_Diagnostics_empty;
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_unsigned_to_nat(5u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_to_nat(x_17);
x_19 = lean_nat_pow(x_15, x_18);
lean_dec(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = lean_usize_to_nat(x_20);
x_22 = lean_mk_empty_array_with_capacity(x_21);
lean_dec(x_21);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_13);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set_usize(x_24, 4, x_17);
x_25 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint64(x_25, sizeof(void*)*1, x_14);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_28);
x_29 = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(x_2, x_3, x_27);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Language_SnapshotTask_get___redArg(x_4);
x_6 = l_Lean_Language_SnapshotTree_forM___redArg(x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_5);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_3, x_1, x_16, x_17, x_7);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_apply_1(x_3, x_5);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_forM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_forM___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_forM___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Language_SnapshotTask_get___redArg(x_4);
x_6 = l_Lean_Language_SnapshotTree_foldM___redArg(x_1, x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_4);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_6, x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_4);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_5);
x_16 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_17 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_3, x_1, x_15, x_16, x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 4, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_apply_2(x_3, x_4, x_6);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Language_SnapshotTree_foldM___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1188_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("printMessageEndPos", 18, 18);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = lean_mk_string_unchecked("print end position of each message in addition to start position", 64, 64);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Language", 8, 8);
x_10 = l_Lean_Name_mkStr3(x_8, x_9, x_2);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_3, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_4, x_5);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_10, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_5, x_15);
x_17 = lean_unbox(x_12);
lean_dec(x_12);
x_5 = x_16;
x_7 = x_17;
x_8 = x_13;
goto _start;
}
else
{
return x_11;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Language_printMessageEndPos;
x_24 = lean_usize_dec_eq(x_5, x_6);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_25 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_2, x_23);
x_48 = lean_array_uget(x_4, x_5);
x_49 = lean_ctor_get(x_48, 4);
lean_inc(x_49);
x_50 = l_Lean_MessageData_kind(x_49);
x_51 = l_Lean_NameMap_find_x3f(lean_box(0), x_3, x_50);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_dec(x_49);
x_26 = x_48;
goto block_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 2);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_48, sizeof(void*)*5);
x_57 = lean_ctor_get_uint8(x_48, sizeof(void*)*5 + 2);
x_58 = lean_ctor_get(x_48, 3);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_59, 4, x_49);
lean_ctor_set_uint8(x_59, sizeof(void*)*5, x_56);
x_60 = lean_unbox(x_52);
lean_dec(x_52);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 1, x_60);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 2, x_57);
x_26 = x_59;
goto block_47;
}
block_47:
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*5 + 2);
if (x_27 == 0)
{
if (x_1 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_26);
x_28 = l_Lean_Message_toString(x_26, x_25, x_8);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_IO_print___at___IO_println___at___Lean_Environment_displayStats_spec__2_spec__2(x_29, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_16 = x_26;
x_17 = x_32;
goto block_22;
}
else
{
uint8_t x_33; 
lean_dec(x_26);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_26);
x_37 = l_Lean_Message_toJson(x_26, x_8);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Json_compress(x_38);
x_41 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_16 = x_26;
x_17 = x_42;
goto block_22;
}
else
{
uint8_t x_43; 
lean_dec(x_26);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
x_16 = x_26;
x_17 = x_8;
goto block_22;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(x_7);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_8);
return x_62;
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_7 = x_9;
x_8 = x_10;
goto _start;
}
block_22:
{
if (x_7 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_ctor_get_uint8(x_16, sizeof(void*)*5 + 1);
lean_dec(x_16);
x_19 = lean_box(x_18);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_9 = x_21;
x_10 = x_17;
goto block_15;
}
else
{
lean_dec(x_19);
x_9 = x_7;
x_10 = x_17;
goto block_15;
}
}
else
{
lean_dec(x_16);
x_9 = x_7;
x_10 = x_17;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_box(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_8);
x_17 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_18 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_7, x_16, x_17, x_5, x_6);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
x_23 = lean_box(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_26 = lean_box(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_20);
x_29 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_30 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_19, x_28, x_29, x_5, x_6);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
x_11 = lean_usize_shift_right(x_5, x_6);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get(x_10, x_9, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_shift_left(x_15, x_6);
x_17 = lean_usize_sub(x_16, x_15);
x_18 = lean_usize_land(x_5, x_17);
x_19 = lean_unsigned_to_nat(5u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_6, x_20);
x_22 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0(x_1, x_2, x_3, x_13, x_18, x_21, x_7, x_8);
lean_dec(x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_26 = lean_array_get_size(x_9);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
return x_22;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_26, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
return x_22;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_22);
x_29 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_unbox(x_23);
lean_dec(x_23);
x_32 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_9, x_29, x_30, x_31, x_24);
return x_32;
}
}
}
else
{
lean_dec(x_12);
return x_22;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_usize_to_nat(x_5);
x_35 = lean_array_get_size(x_33);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_34);
x_37 = lean_box(x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_35, x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
lean_dec(x_34);
x_40 = lean_box(x_7);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
return x_41;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; 
x_42 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_43 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_44 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_33, x_42, x_43, x_7, x_8);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_nat_dec_le(x_10, x_6);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_usize_of_nat(x_6);
x_14 = lean_ctor_get_usize(x_4, 4);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0(x_1, x_2, x_3, x_12, x_13, x_14, x_5, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_8, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
return x_15;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
return x_15;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_15);
x_22 = lean_usize_of_nat(x_8);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_unbox(x_16);
lean_dec(x_16);
x_25 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_18, x_22, x_23, x_24, x_17);
return x_25;
}
}
}
else
{
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_4, 1);
x_27 = lean_nat_sub(x_6, x_10);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
x_30 = lean_box(x_5);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_28, x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_27);
x_33 = lean_box(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_36 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_37 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_26, x_35, x_36, x_5, x_7);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_38, x_5, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 1);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_8, x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
return x_39;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_43, x_43);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
return x_39;
}
else
{
size_t x_46; size_t x_47; uint8_t x_48; lean_object* x_49; 
lean_dec(x_39);
x_46 = lean_usize_of_nat(x_8);
x_47 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_48 = lean_unbox(x_40);
lean_dec(x_40);
x_49 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_42, x_46, x_47, x_48, x_41);
return x_49;
}
}
}
else
{
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0(x_3, x_2, x_4, x_6, x_9, x_8, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__0(x_9, x_2, x_3, x_4, x_10, x_11, x_12, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0_spec__1(x_9, x_2, x_3, x_4, x_10, x_11, x_12, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0_spec__0(x_7, x_2, x_3, x_4, x_8, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0_spec__0(x_9, x_2, x_3, x_4, x_10, x_11, x_12, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_PersistentArray_foldlM___at___Lean_Language_reportMessages_spec__0(x_8, x_2, x_3, x_4, x_9, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Language_reportMessages(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_4, x_5);
x_11 = l_Lean_Language_SnapshotTask_get___redArg(x_10);
x_12 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(x_1, x_2, x_3, x_11, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_18 = lean_unbox(x_13);
lean_dec(x_13);
x_5 = x_17;
x_7 = x_18;
x_8 = x_14;
goto _start;
}
else
{
return x_12;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_20, 0);
x_22 = l_Lean_Language_reportMessages(x_21, x_1, x_2, x_3, x_6);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_unbox(x_24);
lean_dec(x_24);
x_27 = lean_strict_or(x_5, x_26);
x_28 = lean_box(x_27);
lean_inc(x_25);
lean_ctor_set(x_22, 0, x_28);
x_9 = x_22;
x_10 = x_27;
x_11 = x_25;
goto block_19;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_unbox(x_29);
lean_dec(x_29);
x_32 = lean_strict_or(x_5, x_31);
x_33 = lean_box(x_32);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_9 = x_34;
x_10 = x_32;
x_11 = x_30;
goto block_19;
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_9 = x_22;
x_10 = x_37;
x_11 = x_36;
goto block_19;
}
else
{
return x_22;
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_8);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
return x_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
return x_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
lean_dec(x_9);
x_16 = lean_usize_of_nat(x_12);
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(x_1, x_2, x_3, x_8, x_16, x_17, x_10, x_11);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(x_2, x_3, x_4, x_1, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(x_1, x_9, x_3, x_4, x_10, x_11, x_12, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(x_1, x_7, x_3, x_4, x_8, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Language_SnapshotTree_runAndReport(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Language_SnapshotTask_get___redArg(x_6);
x_8 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0(x_7, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_push(x_2, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
return x_5;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_7, x_7);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
return x_5;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_usize_of_nat(x_6);
x_11 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0(x_4, x_10, x_11, x_5);
lean_dec(x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTree_waitAll_go(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_task_pure(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_ctor_get(x_6, 3);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = lean_io_bind_task(x_9, x_8, x_10, x_12, x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTree_waitAll_go___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_to_list(x_3);
x_5 = l_Lean_Language_SnapshotTree_waitAll_go(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Language_instMonadLiftProcessingMProcessingTIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_st_mk_ref(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_mk_string_unchecked("<input>", 7, 7);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_9);
lean_dec(x_9);
x_11 = l_Lean_FileMap_toPosition(x_8, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_box(0);
x_14 = lean_box(2);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_17);
x_19 = lean_unbox(x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_19);
x_20 = lean_unbox(x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_20);
x_21 = lean_unbox(x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 2, x_21);
x_22 = l_Lean_MessageLog_empty;
x_23 = l_Lean_MessageLog_add(x_18, x_22);
x_24 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_23, x_3);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_io_error_to_string(x_10);
x_13 = l_Lean_Language_diagnosticsOfHeaderError(x_12, x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Language_instInhabitedDynamicSnapshot___lam__0___boxed), 1, 0);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Language", 8, 8);
x_19 = lean_mk_string_unchecked("withHeaderExceptions", 20, 20);
x_20 = l_Lean_Name_mkStr3(x_17, x_18, x_19);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Name_toString(x_20, x_22, x_16);
x_24 = lean_box(0);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_unsigned_to_nat(5u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_nat_pow(x_27, x_30);
lean_dec(x_30);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_mk_empty_array_with_capacity(x_33);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set_usize(x_36, 4, x_29);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_26);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_15);
lean_ctor_set(x_39, 2, x_24);
lean_ctor_set(x_39, 3, x_37);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_40);
x_41 = lean_apply_1(x_1, x_39);
lean_ctor_set(x_13, 0, x_41);
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; size_t x_57; lean_object* x_58; lean_object* x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_alloc_closure((void*)(l_Lean_Language_instInhabitedDynamicSnapshot___lam__0___boxed), 1, 0);
x_45 = lean_mk_string_unchecked("Lean", 4, 4);
x_46 = lean_mk_string_unchecked("Language", 8, 8);
x_47 = lean_mk_string_unchecked("withHeaderExceptions", 20, 20);
x_48 = l_Lean_Name_mkStr3(x_45, x_46, x_47);
x_49 = lean_box(1);
x_50 = lean_unbox(x_49);
x_51 = l_Lean_Name_toString(x_48, x_50, x_44);
x_52 = lean_box(0);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_unsigned_to_nat(5u);
x_57 = lean_usize_of_nat(x_56);
x_58 = lean_usize_to_nat(x_57);
x_59 = lean_nat_pow(x_55, x_58);
lean_dec(x_58);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = lean_usize_to_nat(x_60);
x_62 = lean_mk_empty_array_with_capacity(x_61);
lean_dec(x_61);
lean_inc(x_62);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_53);
lean_ctor_set_usize(x_64, 4, x_57);
x_65 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint64(x_65, sizeof(void*)*1, x_54);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_67, 0, x_51);
lean_ctor_set(x_67, 1, x_42);
lean_ctor_set(x_67, 2, x_52);
lean_ctor_set(x_67, 3, x_65);
x_68 = lean_unbox(x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_68);
x_69 = lean_apply_1(x_1, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_43);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Language_withHeaderExceptions___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_st_ref_set(x_1, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_st_mk_ref(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_mkIncrementalProcessor___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Language_Snapshot_instInhabitedDiagnostics = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics);
l_Lean_Language_Snapshot_Diagnostics_empty = _init_l_Lean_Language_Snapshot_Diagnostics_empty();
lean_mark_persistent(l_Lean_Language_Snapshot_Diagnostics_empty);
l_Lean_Language_Snapshot_desc___autoParam = _init_l_Lean_Language_Snapshot_desc___autoParam();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam);
l_Lean_Language_instInhabitedSnapshot = _init_l_Lean_Language_instInhabitedSnapshot();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot);
l_Lean_Language_instInhabitedSnapshotTree = _init_l_Lean_Language_instInhabitedSnapshotTree();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree);
l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_667_ = _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_667_();
lean_mark_persistent(l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_667_);
l_Lean_Language_instTypeNameSnapshotTree = _init_l_Lean_Language_instTypeNameSnapshotTree();
lean_mark_persistent(l_Lean_Language_instTypeNameSnapshotTree);
l_Lean_Language_instToSnapshotTreeSnapshotTree = _init_l_Lean_Language_instToSnapshotTreeSnapshotTree();
lean_mark_persistent(l_Lean_Language_instToSnapshotTreeSnapshotTree);
l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_896_ = _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_896_();
lean_mark_persistent(l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_896_);
l_Lean_Language_instTypeNameSnapshotLeaf = _init_l_Lean_Language_instTypeNameSnapshotLeaf();
lean_mark_persistent(l_Lean_Language_instTypeNameSnapshotLeaf);
l_Lean_Language_instToSnapshotTreeSnapshotLeaf = _init_l_Lean_Language_instToSnapshotTreeSnapshotLeaf();
lean_mark_persistent(l_Lean_Language_instToSnapshotTreeSnapshotLeaf);
l_Lean_Language_instToSnapshotTreeDynamicSnapshot = _init_l_Lean_Language_instToSnapshotTreeDynamicSnapshot();
lean_mark_persistent(l_Lean_Language_instToSnapshotTreeDynamicSnapshot);
l_Lean_Language_instInhabitedDynamicSnapshot = _init_l_Lean_Language_instInhabitedDynamicSnapshot();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot);
if (builtin) {res = l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1188_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_printMessageEndPos = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_printMessageEndPos);
lean_dec_ref(res);
}l_Lean_Language_instMonadLiftProcessingMProcessingTIO = _init_l_Lean_Language_instMonadLiftProcessingMProcessingTIO();
lean_mark_persistent(l_Lean_Language_instMonadLiftProcessingMProcessingTIO);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
