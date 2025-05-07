// Lean compiler output
// Module: Lake.Load.Lean.Elab
// Imports: Lean.Elab.Frontend Lake.DSL.Extensions Lake.DSL.Attributes Lake.Load.Config Lake.Build.Trace Lake.Util.Log
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_896_(lean_object*);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_readModuleData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lake_importModulesUsingCache_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_146_(lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_dirExt;
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lake_instBEqImport__lake;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instInhabitedEnvExtensionState;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
lean_object* l_Lean_mkExtNameMap(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabConfigFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lake_importModulesUsingCache_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_optsExt;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_foldM___at_____private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__3(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lake_LogEntry_ofMessage(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonConfigTrace;
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonConfigTrace;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importEnvCache;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__1(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_96____boxed(lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_bignumToJson(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore_lakeExts;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabConfigFile___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_writeModule(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableImport__lake;
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_truncate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configModuleName;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3(lean_object*, size_t, size_t, uint64_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__1(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0(lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed(lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_96_(lean_object*);
lean_object* lake_environment_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_11 = lean_name_eq(x_3, x_6);
if (x_11 == 0)
{
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_box(0);
if (x_4 == 0)
{
if (x_7 == 0)
{
x_9 = x_11;
goto block_10;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_12);
return x_13;
}
}
else
{
if (x_7 == 0)
{
uint8_t x_14; 
x_14 = lean_unbox(x_12);
return x_14;
}
else
{
x_9 = x_11;
goto block_10;
}
}
}
block_10:
{
if (x_9 == 0)
{
return x_9;
}
else
{
if (x_5 == 0)
{
if (x_8 == 0)
{
return x_9;
}
else
{
return x_5;
}
}
else
{
return x_8;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instBEqImport__lake() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_96_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = lean_uint64_mix_hash(x_6, x_7);
if (x_3 == 0)
{
lean_object* x_18; uint64_t x_19; 
x_18 = lean_unsigned_to_nat(13u);
x_19 = lean_uint64_of_nat(x_18);
x_9 = x_19;
goto block_17;
}
else
{
lean_object* x_20; uint64_t x_21; 
x_20 = lean_unsigned_to_nat(11u);
x_21 = lean_uint64_of_nat(x_20);
x_9 = x_21;
goto block_17;
}
block_17:
{
uint64_t x_10; 
x_10 = lean_uint64_mix_hash(x_8, x_9);
if (x_4 == 0)
{
lean_object* x_11; uint64_t x_12; uint64_t x_13; 
x_11 = lean_unsigned_to_nat(13u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_mix_hash(x_10, x_12);
return x_13;
}
else
{
lean_object* x_14; uint64_t x_15; uint64_t x_16; 
x_14 = lean_unsigned_to_nat(11u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_mix_hash(x_10, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_96____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_96_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instHashableImport__lake() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_96____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_146_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_shiftl(x_2, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_div(x_5, x_6);
lean_dec(x_5);
x_8 = l_Nat_nextPowerOfTwo(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_st_mk_ref(x_11, x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget(x_1, x_7);
x_9 = lean_array_fget(x_2, x_7);
x_10 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_array_get_size(x_4);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg(x_4, x_1, x_7);
if (x_11 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_13; 
lean_inc(x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_array_get_size(x_5);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg(x_5, x_1, x_7);
if (x_11 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_11;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_96_(x_6);
lean_dec(x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_array_get_size(x_1);
x_28 = lean_unsigned_to_nat(7u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_3);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
x_8 = x_29;
goto block_27;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
x_8 = x_29;
goto block_27;
}
else
{
size_t x_34; size_t x_35; uint64_t x_36; 
x_34 = lean_usize_of_nat(x_30);
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3(x_3, x_34, x_35, x_29);
x_8 = x_36;
goto block_27;
}
}
block_27:
{
lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_1, x_22);
if (lean_is_scalar(x_6)) {
 x_24 = lean_alloc_ctor(1, 3, 0);
} else {
 x_24 = x_6;
}
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_array_uset(x_1, x_22, x_24);
x_1 = x_25;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_array_get_size(x_1);
x_28 = lean_unsigned_to_nat(7u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_3);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
x_8 = x_29;
goto block_27;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
x_8 = x_29;
goto block_27;
}
else
{
size_t x_34; size_t x_35; uint64_t x_36; 
x_34 = lean_usize_of_nat(x_30);
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3(x_3, x_34, x_35, x_29);
x_8 = x_36;
goto block_27;
}
}
block_27:
{
lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_1, x_22);
if (lean_is_scalar(x_6)) {
 x_24 = lean_alloc_ctor(1, 3, 0);
} else {
 x_24 = x_6;
}
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_array_uset(x_1, x_22, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4_spec__4___redArg(x_25, x_5);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lake_importModulesUsingCache_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_11 = lean_array_get_size(x_4);
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
goto block_10;
}
else
{
uint8_t x_14; 
x_14 = l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg(x_4, x_1, x_11);
if (x_14 == 0)
{
goto block_10;
}
else
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_6);
return x_15;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_DHashMap_Internal_AssocList_replace___at___Lake_importModulesUsingCache_spec__8___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(1, 3, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lake_importModulesUsingCache_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lake_importModulesUsingCache_spec__8___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; size_t x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_105; uint64_t x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_5 = l_Lake_importEnvCache;
x_53 = lean_st_ref_get(x_5, x_4);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_array_get_size(x_57);
x_105 = lean_unsigned_to_nat(7u);
x_106 = lean_uint64_of_nat(x_105);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_array_get_size(x_1);
x_109 = lean_nat_dec_lt(x_107, x_108);
if (x_109 == 0)
{
lean_dec(x_108);
x_59 = x_106;
goto block_104;
}
else
{
uint8_t x_110; 
x_110 = lean_nat_dec_le(x_108, x_108);
if (x_110 == 0)
{
lean_dec(x_108);
x_59 = x_106;
goto block_104;
}
else
{
size_t x_111; size_t x_112; uint64_t x_113; 
x_111 = lean_usize_of_nat(x_107);
x_112 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_113 = l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3(x_1, x_111, x_112, x_106);
x_59 = x_113;
goto block_104;
}
}
block_14:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_set(x_5, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
block_52:
{
uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_uint64_shift_right(x_24, x_20);
x_26 = lean_uint64_xor(x_24, x_25);
x_27 = lean_uint64_shift_right(x_26, x_17);
x_28 = lean_uint64_xor(x_26, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_31 = lean_usize_sub(x_30, x_19);
x_32 = lean_usize_land(x_29, x_31);
x_33 = lean_array_uget(x_23, x_32);
x_34 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___redArg(x_1, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_nat_add(x_18, x_22);
lean_dec(x_18);
lean_inc(x_15);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_15);
lean_ctor_set(x_36, 2, x_33);
x_37 = lean_array_uset(x_23, x_32, x_36);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_shiftl(x_35, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3___redArg(x_37);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_44);
x_6 = x_15;
x_7 = x_21;
x_8 = x_45;
goto block_14;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_37);
x_6 = x_15;
x_7 = x_21;
x_8 = x_46;
goto block_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_box(0);
x_48 = lean_array_uset(x_23, x_32, x_47);
lean_inc(x_15);
x_49 = l_Std_DHashMap_Internal_AssocList_replace___at___Lake_importModulesUsingCache_spec__8___redArg(x_1, x_15, x_33);
x_50 = lean_array_uset(x_48, x_32, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_50);
x_6 = x_15;
x_7 = x_21;
x_8 = x_51;
goto block_14;
}
}
block_104:
{
lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; lean_object* x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_unsigned_to_nat(32u);
x_61 = lean_uint64_of_nat(x_60);
x_62 = lean_uint64_shift_right(x_59, x_61);
x_63 = lean_uint64_xor(x_59, x_62);
x_64 = lean_unsigned_to_nat(16u);
x_65 = lean_uint64_of_nat(x_64);
x_66 = lean_uint64_shift_right(x_63, x_65);
x_67 = lean_uint64_xor(x_63, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_usize_of_nat(x_70);
x_72 = lean_usize_sub(x_69, x_71);
x_73 = lean_usize_land(x_68, x_72);
x_74 = lean_array_uget(x_57, x_73);
lean_dec(x_57);
x_75 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___redArg(x_1, x_74);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; 
lean_dec(x_56);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_mk_empty_array_with_capacity(x_76);
x_78 = lean_box(0);
x_79 = lean_box(1);
x_80 = lean_box(2);
x_81 = lean_box(0);
x_82 = lean_unbox(x_78);
x_83 = lean_unbox(x_79);
x_84 = lean_unbox(x_80);
lean_inc(x_1);
x_85 = l_Lean_importModules(x_1, x_2, x_3, x_77, x_82, x_83, x_84, x_81, x_55);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint64_t x_95; lean_object* x_96; uint8_t x_97; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_st_ref_take(x_5, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_array_get_size(x_92);
x_94 = lean_unsigned_to_nat(7u);
x_95 = lean_uint64_of_nat(x_94);
x_96 = lean_array_get_size(x_1);
x_97 = lean_nat_dec_lt(x_76, x_96);
if (x_97 == 0)
{
lean_dec(x_96);
x_15 = x_86;
x_16 = x_93;
x_17 = x_65;
x_18 = x_91;
x_19 = x_71;
x_20 = x_61;
x_21 = x_90;
x_22 = x_70;
x_23 = x_92;
x_24 = x_95;
goto block_52;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
lean_dec(x_96);
x_15 = x_86;
x_16 = x_93;
x_17 = x_65;
x_18 = x_91;
x_19 = x_71;
x_20 = x_61;
x_21 = x_90;
x_22 = x_70;
x_23 = x_92;
x_24 = x_95;
goto block_52;
}
else
{
size_t x_99; size_t x_100; uint64_t x_101; 
x_99 = lean_usize_of_nat(x_76);
x_100 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_101 = l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3(x_1, x_99, x_100, x_95);
x_15 = x_86;
x_16 = x_93;
x_17 = x_65;
x_18 = x_91;
x_19 = x_71;
x_20 = x_61;
x_21 = x_90;
x_22 = x_70;
x_23 = x_92;
x_24 = x_101;
goto block_52;
}
}
}
else
{
lean_dec(x_1);
return x_85;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_75, 0);
lean_inc(x_102);
lean_dec(x_75);
if (lean_is_scalar(x_56)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_56;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_55);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lake_importModulesUsingCache_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_importModulesUsingCache_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_importModulesUsingCache_spec__3_spec__3_spec__3(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = l_Lake_importModulesUsingCache(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_processHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
lean_inc(x_1);
x_6 = l_Lean_Elab_HeaderSyntax_imports(x_1);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_uint32_of_nat(x_7);
x_9 = l_Lake_importModulesUsingCache(x_6, x_2, x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_61; lean_object* x_62; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
x_20 = lean_box(0);
x_61 = lean_unbox(x_20);
x_62 = l_Lean_Syntax_getPos_x3f(x_1, x_61);
lean_dec(x_1);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_unsigned_to_nat(0u);
x_21 = x_63;
goto block_60;
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_21 = x_64;
goto block_60;
}
block_60:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; 
x_22 = lean_io_error_to_string(x_17);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_uint32_of_nat(x_24);
x_26 = lean_mk_empty_environment(x_25, x_18);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_FileMap_toPosition(x_19, x_21);
lean_dec(x_21);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_box(2);
x_33 = lean_mk_string_unchecked("", 0, 0);
x_34 = l_Lean_MessageData_ofFormat(x_23);
x_35 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
x_36 = lean_unbox(x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_36);
x_37 = lean_unbox(x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 1, x_37);
x_38 = lean_unbox(x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 2, x_38);
x_39 = l_Lean_MessageLog_add(x_35, x_4);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_26, 0, x_40);
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = l_Lean_FileMap_toPosition(x_19, x_21);
lean_dec(x_21);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = lean_box(2);
x_47 = lean_mk_string_unchecked("", 0, 0);
x_48 = l_Lean_MessageData_ofFormat(x_23);
x_49 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set(x_49, 4, x_48);
x_50 = lean_unbox(x_20);
lean_ctor_set_uint8(x_49, sizeof(void*)*5, x_50);
x_51 = lean_unbox(x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*5 + 1, x_51);
x_52 = lean_unbox(x_20);
lean_ctor_set_uint8(x_49, sizeof(void*)*5 + 2, x_52);
x_53 = l_Lean_MessageLog_add(x_49, x_4);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_42);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_26);
if (x_56 == 0)
{
return x_26;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_26, 0);
x_58 = lean_ctor_get(x_26, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_26);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
static lean_object* _init_l_Lake_configModuleName() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("lakefile", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_10 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0(x_1, x_9, x_6, x_7);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_13;
x_6 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_10 = lean_apply_3(x_1, x_9, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_13;
x_6 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_6);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__0(x_1, x_5, x_15, x_16, x_8, x_3, x_4);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_18);
x_21 = lean_box(0);
x_22 = lean_nat_dec_lt(x_19, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_20, x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_19);
x_29 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_30 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1(x_1, x_18, x_28, x_29, x_21, x_3, x_4);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_6 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0(x_1, x_5, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_box(0);
x_18 = lean_nat_dec_lt(x_15, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_17);
return x_6;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_16, x_16);
if (x_19 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_7, 0, x_17);
return x_6;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_free_object(x_7);
lean_free_object(x_6);
x_20 = lean_usize_of_nat(x_15);
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1(x_1, x_14, x_20, x_21, x_17, x_12, x_9);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get_size(x_24);
x_27 = lean_box(0);
x_28 = lean_nat_dec_lt(x_25, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_6, 0, x_29);
return x_6;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_26, x_26);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
lean_free_object(x_6);
x_32 = lean_usize_of_nat(x_25);
x_33 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_34 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1(x_1, x_24, x_32, x_33, x_27, x_23, x_9);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_37 = x_7;
} else {
 lean_dec_ref(x_7);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_array_get_size(x_38);
x_41 = lean_box(0);
x_42 = lean_nat_dec_lt(x_39, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_1);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_36);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_40, x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_40);
lean_dec(x_1);
if (lean_is_scalar(x_37)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_37;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_36);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
return x_47;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
lean_dec(x_37);
x_48 = lean_usize_of_nat(x_39);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1(x_1, x_38, x_48, x_49, x_41, x_36, x_35);
return x_50;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0(x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_elabConfigFile___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lake_LogEntry_ofMessage(x_1, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
x_9 = lean_array_push(x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_array_push(x_2, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_elabConfigFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_readFile(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_4);
x_12 = l_Lean_Parser_mkInputContext(x_8, x_4, x_11);
lean_inc(x_12);
x_13 = l_Lean_Parser_parseHeader(x_12, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_12);
lean_inc(x_3);
x_21 = l_Lake_processHeader(x_17, x_3, x_12, x_20, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lake_configModuleName;
x_27 = l_Lean_Environment_setMainModule(x_24, x_26);
x_28 = l_Lake_dirExt;
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_1);
x_30 = l_Lean_EnvExtension_setState___redArg(x_28, x_27, x_29);
x_31 = l_Lake_optsExt;
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_2);
x_33 = l_Lean_EnvExtension_setState___redArg(x_31, x_30, x_32);
x_34 = l_Lean_Elab_Command_mkState(x_33, x_25, x_3);
x_35 = l_Lean_Elab_IO_processCommands(x_12, x_19, x_34, x_23);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_closure((void*)(l_Lake_elabConfigFile___lam__0), 3, 0);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = l_Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0(x_40, x_38, x_5, x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
x_48 = l_Lean_MessageLog_hasErrors(x_40);
lean_dec(x_40);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_4);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
lean_ctor_set(x_42, 0, x_49);
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_39);
x_50 = lean_mk_string_unchecked(": package configuration has errors", 34, 34);
x_51 = lean_string_append(x_4, x_50);
lean_dec(x_50);
x_52 = lean_box(3);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = lean_array_get_size(x_46);
x_56 = lean_array_push(x_46, x_53);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_56);
lean_ctor_set(x_42, 0, x_55);
return x_41;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_dec(x_42);
x_58 = l_Lean_MessageLog_hasErrors(x_40);
lean_dec(x_40);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_4);
x_59 = lean_ctor_get(x_39, 0);
lean_inc(x_59);
lean_dec(x_39);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_41, 0, x_60);
return x_41;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_39);
x_61 = lean_mk_string_unchecked(": package configuration has errors", 34, 34);
x_62 = lean_string_append(x_4, x_61);
lean_dec(x_61);
x_63 = lean_box(3);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_unbox(x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = lean_array_get_size(x_57);
x_67 = lean_array_push(x_57, x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_41, 0, x_68);
return x_41;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_41, 1);
lean_inc(x_69);
lean_dec(x_41);
x_70 = lean_ctor_get(x_42, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_71 = x_42;
} else {
 lean_dec_ref(x_42);
 x_71 = lean_box(0);
}
x_72 = l_Lean_MessageLog_hasErrors(x_40);
lean_dec(x_40);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_4);
x_73 = lean_ctor_get(x_39, 0);
lean_inc(x_73);
lean_dec(x_39);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_39);
x_76 = lean_mk_string_unchecked(": package configuration has errors", 34, 34);
x_77 = lean_string_append(x_4, x_76);
lean_dec(x_76);
x_78 = lean_box(3);
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
x_80 = lean_unbox(x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_80);
x_81 = lean_array_get_size(x_70);
x_82 = lean_array_push(x_70, x_79);
if (lean_is_scalar(x_71)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_71;
 lean_ctor_set_tag(x_83, 1);
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_69);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_41, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_42);
if (x_87 == 0)
{
return x_41;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_42, 0);
x_89 = lean_ctor_get(x_42, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_42);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_41, 0, x_90);
return x_41;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_41, 1);
lean_inc(x_91);
lean_dec(x_41);
x_92 = lean_ctor_get(x_42, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_42, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_94 = x_42;
} else {
 lean_dec_ref(x_42);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_21);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_21, 0);
x_99 = lean_io_error_to_string(x_98);
x_100 = lean_box(3);
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_99);
x_102 = lean_unbox(x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_102);
x_103 = lean_array_get_size(x_5);
x_104 = lean_array_push(x_5, x_101);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_104);
lean_ctor_set(x_15, 0, x_103);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_15);
return x_21;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_21, 0);
x_106 = lean_ctor_get(x_21, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_21);
x_107 = lean_io_error_to_string(x_105);
x_108 = lean_box(3);
x_109 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_unbox(x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_110);
x_111 = lean_array_get_size(x_5);
x_112 = lean_array_push(x_5, x_109);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_112);
lean_ctor_set(x_15, 0, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_15);
lean_ctor_set(x_113, 1, x_106);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_15, 0);
x_115 = lean_ctor_get(x_15, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_3);
x_116 = l_Lake_processHeader(x_17, x_3, x_12, x_115, x_16);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = l_Lake_configModuleName;
x_122 = l_Lean_Environment_setMainModule(x_119, x_121);
x_123 = l_Lake_dirExt;
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_1);
x_125 = l_Lean_EnvExtension_setState___redArg(x_123, x_122, x_124);
x_126 = l_Lake_optsExt;
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_2);
x_128 = l_Lean_EnvExtension_setState___redArg(x_126, x_125, x_127);
x_129 = l_Lean_Elab_Command_mkState(x_128, x_120, x_3);
x_130 = l_Lean_Elab_IO_processCommands(x_12, x_114, x_129, x_118);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_alloc_closure((void*)(l_Lake_elabConfigFile___lam__0), 3, 0);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = l_Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0(x_135, x_133, x_5, x_132);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_141 = x_137;
} else {
 lean_dec_ref(x_137);
 x_141 = lean_box(0);
}
x_142 = l_Lean_MessageLog_hasErrors(x_135);
lean_dec(x_135);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_4);
x_143 = lean_ctor_get(x_134, 0);
lean_inc(x_143);
lean_dec(x_134);
if (lean_is_scalar(x_141)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_141;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_140);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_139;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_138);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_134);
x_146 = lean_mk_string_unchecked(": package configuration has errors", 34, 34);
x_147 = lean_string_append(x_4, x_146);
lean_dec(x_146);
x_148 = lean_box(3);
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
x_150 = lean_unbox(x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_150);
x_151 = lean_array_get_size(x_140);
x_152 = lean_array_push(x_140, x_149);
if (lean_is_scalar(x_141)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_141;
 lean_ctor_set_tag(x_153, 1);
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
if (lean_is_scalar(x_139)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_139;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_138);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_4);
x_155 = lean_ctor_get(x_136, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_156 = x_136;
} else {
 lean_dec_ref(x_136);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_137, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_137, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_159 = x_137;
} else {
 lean_dec_ref(x_137);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
if (lean_is_scalar(x_156)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_156;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_155);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_116, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_116, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_164 = x_116;
} else {
 lean_dec_ref(x_116);
 x_164 = lean_box(0);
}
x_165 = lean_io_error_to_string(x_162);
x_166 = lean_box(3);
x_167 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_167, 0, x_165);
x_168 = lean_unbox(x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_168);
x_169 = lean_array_get_size(x_5);
x_170 = lean_array_push(x_5, x_167);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
if (lean_is_scalar(x_164)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_164;
 lean_ctor_set_tag(x_172, 0);
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_163);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_13);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_ctor_get(x_13, 0);
x_175 = lean_io_error_to_string(x_174);
x_176 = lean_box(3);
x_177 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_177, 0, x_175);
x_178 = lean_unbox(x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_178);
x_179 = lean_array_get_size(x_5);
x_180 = lean_array_push(x_5, x_177);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_181);
return x_13;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_182 = lean_ctor_get(x_13, 0);
x_183 = lean_ctor_get(x_13, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_13);
x_184 = lean_io_error_to_string(x_182);
x_185 = lean_box(3);
x_186 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_186, 0, x_184);
x_187 = lean_unbox(x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_187);
x_188 = lean_array_get_size(x_5);
x_189 = lean_array_push(x_5, x_186);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_183);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_7);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_193 = lean_ctor_get(x_7, 0);
x_194 = lean_io_error_to_string(x_193);
x_195 = lean_box(3);
x_196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_196, 0, x_194);
x_197 = lean_unbox(x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_197);
x_198 = lean_array_get_size(x_5);
x_199 = lean_array_push(x_5, x_196);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_200);
return x_7;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_201 = lean_ctor_get(x_7, 0);
x_202 = lean_ctor_get(x_7, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_7);
x_203 = lean_io_error_to_string(x_201);
x_204 = lean_box(3);
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
x_206 = lean_unbox(x_204);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_206);
x_207 = lean_array_get_size(x_5);
x_208 = lean_array_push(x_5, x_205);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_202);
return x_210;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forMAux___at___Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forM___at___Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageLog_forM___at___Lake_elabConfigFile_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lake_environment_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_1 = lean_box(0);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("packageAttr", 11, 11);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = l_Lean_NameSet_insert(x_1, x_4);
x_6 = lean_mk_string_unchecked("packageDepAttr", 14, 14);
lean_inc(x_2);
x_7 = l_Lean_Name_mkStr2(x_2, x_6);
x_8 = l_Lean_NameSet_insert(x_5, x_7);
x_9 = lean_mk_string_unchecked("postUpdateAttr", 14, 14);
lean_inc(x_2);
x_10 = l_Lean_Name_mkStr2(x_2, x_9);
x_11 = l_Lean_NameSet_insert(x_8, x_10);
x_12 = lean_mk_string_unchecked("scriptAttr", 10, 10);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr2(x_2, x_12);
x_14 = l_Lean_NameSet_insert(x_11, x_13);
x_15 = lean_mk_string_unchecked("defaultScriptAttr", 17, 17);
lean_inc(x_2);
x_16 = l_Lean_Name_mkStr2(x_2, x_15);
x_17 = l_Lean_NameSet_insert(x_14, x_16);
x_18 = lean_mk_string_unchecked("leanLibAttr", 11, 11);
lean_inc(x_2);
x_19 = l_Lean_Name_mkStr2(x_2, x_18);
x_20 = l_Lean_NameSet_insert(x_17, x_19);
x_21 = lean_mk_string_unchecked("leanExeAttr", 11, 11);
lean_inc(x_2);
x_22 = l_Lean_Name_mkStr2(x_2, x_21);
x_23 = l_Lean_NameSet_insert(x_20, x_22);
x_24 = lean_mk_string_unchecked("externLibAttr", 13, 13);
lean_inc(x_2);
x_25 = l_Lean_Name_mkStr2(x_2, x_24);
x_26 = l_Lean_NameSet_insert(x_23, x_25);
x_27 = lean_mk_string_unchecked("targetAttr", 10, 10);
lean_inc(x_2);
x_28 = l_Lean_Name_mkStr2(x_2, x_27);
x_29 = l_Lean_NameSet_insert(x_26, x_28);
x_30 = lean_mk_string_unchecked("defaultTargetAttr", 17, 17);
lean_inc(x_2);
x_31 = l_Lean_Name_mkStr2(x_2, x_30);
x_32 = l_Lean_NameSet_insert(x_29, x_31);
x_33 = lean_mk_string_unchecked("testDriverAttr", 14, 14);
lean_inc(x_2);
x_34 = l_Lean_Name_mkStr2(x_2, x_33);
x_35 = l_Lean_NameSet_insert(x_32, x_34);
x_36 = lean_mk_string_unchecked("lintDriverAttr", 14, 14);
lean_inc(x_2);
x_37 = l_Lean_Name_mkStr2(x_2, x_36);
x_38 = l_Lean_NameSet_insert(x_35, x_37);
x_39 = lean_mk_string_unchecked("moduleFacetAttr", 15, 15);
lean_inc(x_2);
x_40 = l_Lean_Name_mkStr2(x_2, x_39);
x_41 = l_Lean_NameSet_insert(x_38, x_40);
x_42 = lean_mk_string_unchecked("packageFacetAttr", 16, 16);
lean_inc(x_2);
x_43 = l_Lean_Name_mkStr2(x_2, x_42);
x_44 = l_Lean_NameSet_insert(x_41, x_43);
x_45 = lean_mk_string_unchecked("libraryFacetAttr", 16, 16);
x_46 = l_Lean_Name_mkStr2(x_2, x_45);
x_47 = l_Lean_NameSet_insert(x_44, x_46);
x_48 = lean_mk_string_unchecked("Lean", 4, 4);
x_49 = lean_mk_string_unchecked("docStringExt", 12, 12);
lean_inc(x_48);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = l_Lean_NameSet_insert(x_47, x_50);
x_52 = lean_mk_string_unchecked("IR", 2, 2);
x_53 = lean_mk_string_unchecked("declMapExt", 10, 10);
x_54 = l_Lean_Name_mkStr3(x_48, x_52, x_53);
x_55 = l_Lean_NameSet_insert(x_51, x_54);
return x_55;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_array_uget(x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lake_importConfigFileCore_lakeExts;
x_18 = l_Lean_NameSet_contains(x_17, x_15);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_15);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; lean_object* x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_array_get_size(x_19);
x_21 = l_Lean_Name_hash___override(x_15);
x_22 = lean_unsigned_to_nat(32u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_unsigned_to_nat(16u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = lean_uint64_shift_right(x_25, x_27);
x_29 = lean_uint64_xor(x_25, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_sub(x_31, x_33);
x_35 = lean_usize_land(x_30, x_34);
x_36 = lean_array_uget(x_19, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_15, x_36);
lean_dec(x_36);
lean_dec(x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_dec(x_16);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_instInhabitedEnvExtensionState;
x_41 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_40);
x_42 = lean_array_get_size(x_16);
x_43 = lean_nat_dec_lt(x_39, x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_16);
x_7 = x_6;
goto block_12;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_42, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_16);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
x_45 = lean_array_get(x_41, x_2, x_38);
lean_dec(x_38);
x_46 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_addEntry), 6, 4);
lean_closure_set(x_46, 0, lean_box(0));
lean_closure_set(x_46, 1, lean_box(0));
lean_closure_set(x_46, 2, lean_box(0));
lean_closure_set(x_46, 3, x_45);
x_47 = lean_usize_of_nat(x_39);
x_48 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_49 = l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__0(x_46, x_16, x_47, x_48, x_6);
lean_dec(x_16);
x_7 = x_49;
goto block_12;
}
}
}
}
}
else
{
return x_6;
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_array_uget(x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lake_importConfigFileCore_lakeExts;
x_18 = l_Lean_NameSet_contains(x_17, x_15);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_15);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; lean_object* x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_array_get_size(x_19);
x_21 = l_Lean_Name_hash___override(x_15);
x_22 = lean_unsigned_to_nat(32u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_unsigned_to_nat(16u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = lean_uint64_shift_right(x_25, x_27);
x_29 = lean_uint64_xor(x_25, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_sub(x_31, x_33);
x_35 = lean_usize_land(x_30, x_34);
x_36 = lean_array_uget(x_19, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_15, x_36);
lean_dec(x_36);
lean_dec(x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_dec(x_16);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_instInhabitedEnvExtensionState;
x_41 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_40);
x_42 = lean_array_get_size(x_16);
x_43 = lean_nat_dec_lt(x_39, x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_16);
x_7 = x_6;
goto block_12;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_42, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_16);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
x_45 = lean_array_get(x_41, x_2, x_38);
lean_dec(x_38);
x_46 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_addEntry), 6, 4);
lean_closure_set(x_46, 0, lean_box(0));
lean_closure_set(x_46, 1, lean_box(0));
lean_closure_set(x_46, 2, lean_box(0));
lean_closure_set(x_46, 3, x_45);
x_47 = lean_usize_of_nat(x_39);
x_48 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_49 = l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__0(x_46, x_16, x_47, x_48, x_6);
lean_dec(x_16);
x_7 = x_49;
goto block_12;
}
}
}
}
}
else
{
return x_6;
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_4, x_9);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1_spec__1(x_1, x_2, x_3, x_10, x_5, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lake_environment_add(x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_readModuleData(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_uint32_of_nat(x_9);
x_11 = l_Lake_importModulesUsingCache(x_8, x_2, x_10, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_persistentEnvExtensionsRef;
x_15 = lean_st_ref_get(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_mkExtNameMap(x_18, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_35 = lean_ctor_get(x_7, 2);
lean_inc(x_35);
x_36 = lean_array_get_size(x_35);
x_37 = lean_nat_dec_lt(x_18, x_36);
if (x_37 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
x_23 = x_12;
goto block_34;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_36, x_36);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
x_23 = x_12;
goto block_34;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = lean_usize_of_nat(x_18);
x_40 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_41 = l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__3(x_35, x_39, x_40, x_12);
lean_dec(x_35);
x_23 = x_41;
goto block_34;
}
}
block_34:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_7, 4);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_array_get_size(x_24);
x_26 = lean_nat_dec_lt(x_18, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_16);
if (lean_is_scalar(x_22)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_22;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_25, x_25);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_16);
if (lean_is_scalar(x_22)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_22;
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_usize_of_nat(x_18);
x_31 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_32 = l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1(x_20, x_16, x_24, x_30, x_31, x_23);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_20);
if (lean_is_scalar(x_22)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_22;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
return x_33;
}
}
}
}
else
{
lean_dec(x_7);
return x_11;
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_4);
if (x_42 == 0)
{
return x_4;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_4);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1_spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_importConfigFileCore_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_896_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_2 = lean_mk_string_unchecked("platform", 8, 8);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_mk_string_unchecked("leanHash", 8, 8);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked("configHash", 10, 10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_unbox_uint64(x_11);
lean_dec(x_11);
x_13 = lean_uint64_to_nat(x_12);
x_14 = l_Lean_bignumToJson(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_mk_string_unchecked("options", 7, 7);
x_22 = lean_box(0);
x_23 = l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0(x_22, x_16);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_31, x_33);
x_35 = l_Lean_Json_mkObj(x_34);
return x_35;
}
}
static lean_object* _init_l_Lake_instToJsonConfigTrace() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_896_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_bignumFromJson_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_cstr_to_nat("18446744073709551616");
x_11 = lean_nat_dec_le(x_10, x_9);
lean_dec(x_10);
if (x_11 == 0)
{
uint64_t x_12; lean_object* x_13; 
x_12 = lean_uint64_of_nat(x_9);
lean_dec(x_9);
x_13 = lean_box_uint64(x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_cstr_to_nat("18446744073709551616");
x_17 = lean_nat_dec_le(x_16, x_15);
lean_dec(x_16);
if (x_17 == 0)
{
uint64_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_uint64_of_nat(x_15);
lean_dec(x_15);
x_19 = lean_box_uint64(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_21 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_foldM___at_____private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115__spec__0(x_5, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
x_8 = lean_unsigned_to_nat(80u);
x_9 = l_Lean_Json_pretty(x_3, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("'", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("platform", 8, 8);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lake", 4, 4);
x_8 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_6);
x_12 = l_Lean_Name_toString(x_9, x_11, x_6);
x_13 = lean_mk_string_unchecked(".", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_Name_mkStr1(x_2);
x_16 = lean_unbox(x_10);
x_17 = l_Lean_Name_toString(x_15, x_16, x_6);
x_18 = lean_string_append(x_14, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked(": ", 2, 2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed), 1, 0);
x_24 = lean_mk_string_unchecked("Lake", 4, 4);
x_25 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
lean_inc(x_23);
x_29 = l_Lean_Name_toString(x_26, x_28, x_23);
x_30 = lean_mk_string_unchecked(".", 1, 1);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Lean_Name_mkStr1(x_2);
x_33 = lean_unbox(x_27);
x_34 = l_Lean_Name_toString(x_32, x_33, x_23);
x_35 = lean_string_append(x_31, x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked(": ", 2, 2);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_37, x_22);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_mk_string_unchecked("leanHash", 8, 8);
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_43);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed), 1, 0);
x_49 = lean_mk_string_unchecked("Lake", 4, 4);
x_50 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
x_51 = l_Lean_Name_mkStr2(x_49, x_50);
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
lean_inc(x_48);
x_54 = l_Lean_Name_toString(x_51, x_53, x_48);
x_55 = lean_mk_string_unchecked(".", 1, 1);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = l_Lean_Name_mkStr1(x_44);
x_58 = lean_unbox(x_52);
x_59 = l_Lean_Name_toString(x_57, x_58, x_48);
x_60 = lean_string_append(x_56, x_59);
lean_dec(x_59);
x_61 = lean_mk_string_unchecked(": ", 2, 2);
x_62 = lean_string_append(x_60, x_61);
lean_dec(x_61);
x_63 = lean_string_append(x_62, x_47);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_63);
return x_45;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed), 1, 0);
x_66 = lean_mk_string_unchecked("Lake", 4, 4);
x_67 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
x_68 = l_Lean_Name_mkStr2(x_66, x_67);
x_69 = lean_box(1);
x_70 = lean_unbox(x_69);
lean_inc(x_65);
x_71 = l_Lean_Name_toString(x_68, x_70, x_65);
x_72 = lean_mk_string_unchecked(".", 1, 1);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = l_Lean_Name_mkStr1(x_44);
x_75 = lean_unbox(x_69);
x_76 = l_Lean_Name_toString(x_74, x_75, x_65);
x_77 = lean_string_append(x_73, x_76);
lean_dec(x_76);
x_78 = lean_mk_string_unchecked(": ", 2, 2);
x_79 = lean_string_append(x_77, x_78);
lean_dec(x_78);
x_80 = lean_string_append(x_79, x_64);
lean_dec(x_64);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
else
{
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_82; 
lean_dec(x_43);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_45);
if (x_82 == 0)
{
lean_ctor_set_tag(x_45, 0);
return x_45;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_45, 0);
lean_inc(x_83);
lean_dec(x_45);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_45, 0);
lean_inc(x_85);
lean_dec(x_45);
x_86 = lean_mk_string_unchecked("configHash", 10, 10);
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__0(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed), 1, 0);
x_91 = lean_mk_string_unchecked("Lake", 4, 4);
x_92 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = lean_box(1);
x_95 = lean_unbox(x_94);
lean_inc(x_90);
x_96 = l_Lean_Name_toString(x_93, x_95, x_90);
x_97 = lean_mk_string_unchecked(".", 1, 1);
x_98 = lean_string_append(x_96, x_97);
lean_dec(x_97);
x_99 = l_Lean_Name_mkStr1(x_86);
x_100 = lean_unbox(x_94);
x_101 = l_Lean_Name_toString(x_99, x_100, x_90);
x_102 = lean_string_append(x_98, x_101);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked(": ", 2, 2);
x_104 = lean_string_append(x_102, x_103);
lean_dec(x_103);
x_105 = lean_string_append(x_104, x_89);
lean_dec(x_89);
lean_ctor_set(x_87, 0, x_105);
return x_87;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
lean_dec(x_87);
x_107 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed), 1, 0);
x_108 = lean_mk_string_unchecked("Lake", 4, 4);
x_109 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
x_110 = l_Lean_Name_mkStr2(x_108, x_109);
x_111 = lean_box(1);
x_112 = lean_unbox(x_111);
lean_inc(x_107);
x_113 = l_Lean_Name_toString(x_110, x_112, x_107);
x_114 = lean_mk_string_unchecked(".", 1, 1);
x_115 = lean_string_append(x_113, x_114);
lean_dec(x_114);
x_116 = l_Lean_Name_mkStr1(x_86);
x_117 = lean_unbox(x_111);
x_118 = l_Lean_Name_toString(x_116, x_117, x_107);
x_119 = lean_string_append(x_115, x_118);
lean_dec(x_118);
x_120 = lean_mk_string_unchecked(": ", 2, 2);
x_121 = lean_string_append(x_119, x_120);
lean_dec(x_120);
x_122 = lean_string_append(x_121, x_106);
lean_dec(x_106);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_124; 
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_87);
if (x_124 == 0)
{
lean_ctor_set_tag(x_87, 0);
return x_87;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_87, 0);
lean_inc(x_125);
lean_dec(x_87);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_87, 0);
lean_inc(x_127);
lean_dec(x_87);
x_128 = lean_mk_string_unchecked("options", 7, 7);
x_129 = l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__1(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed), 1, 0);
x_133 = lean_mk_string_unchecked("Lake", 4, 4);
x_134 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
x_135 = l_Lean_Name_mkStr2(x_133, x_134);
x_136 = lean_box(1);
x_137 = lean_unbox(x_136);
lean_inc(x_132);
x_138 = l_Lean_Name_toString(x_135, x_137, x_132);
x_139 = lean_mk_string_unchecked(".", 1, 1);
x_140 = lean_string_append(x_138, x_139);
lean_dec(x_139);
x_141 = l_Lean_Name_mkStr1(x_128);
x_142 = lean_unbox(x_136);
x_143 = l_Lean_Name_toString(x_141, x_142, x_132);
x_144 = lean_string_append(x_140, x_143);
lean_dec(x_143);
x_145 = lean_mk_string_unchecked(": ", 2, 2);
x_146 = lean_string_append(x_144, x_145);
lean_dec(x_145);
x_147 = lean_string_append(x_146, x_131);
lean_dec(x_131);
lean_ctor_set(x_129, 0, x_147);
return x_129;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
lean_dec(x_129);
x_149 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed), 1, 0);
x_150 = lean_mk_string_unchecked("Lake", 4, 4);
x_151 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
x_152 = l_Lean_Name_mkStr2(x_150, x_151);
x_153 = lean_box(1);
x_154 = lean_unbox(x_153);
lean_inc(x_149);
x_155 = l_Lean_Name_toString(x_152, x_154, x_149);
x_156 = lean_mk_string_unchecked(".", 1, 1);
x_157 = lean_string_append(x_155, x_156);
lean_dec(x_156);
x_158 = l_Lean_Name_mkStr1(x_128);
x_159 = lean_unbox(x_153);
x_160 = l_Lean_Name_toString(x_158, x_159, x_149);
x_161 = lean_string_append(x_157, x_160);
lean_dec(x_160);
x_162 = lean_mk_string_unchecked(": ", 2, 2);
x_163 = lean_string_append(x_161, x_162);
lean_dec(x_162);
x_164 = lean_string_append(x_163, x_148);
lean_dec(x_148);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
else
{
lean_dec(x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_166; 
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
x_166 = !lean_is_exclusive(x_129);
if (x_166 == 0)
{
lean_ctor_set_tag(x_129, 0);
return x_129;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_129, 0);
lean_inc(x_167);
lean_dec(x_129);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_129);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_129, 0);
x_171 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_171, 0, x_43);
lean_ctor_set(x_171, 1, x_85);
lean_ctor_set(x_171, 2, x_127);
lean_ctor_set(x_171, 3, x_170);
lean_ctor_set(x_129, 0, x_171);
return x_129;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_129, 0);
lean_inc(x_172);
lean_dec(x_129);
x_173 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_173, 0, x_43);
lean_ctor_set(x_173, 1, x_85);
lean_ctor_set(x_173, 2, x_127);
lean_ctor_set(x_173, 3, x_172);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976__spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace___lam__0____x40_Lake_Load_Lean_Elab___hyg_976_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instFromJsonConfigTrace() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = lean_io_prim_handle_mk(x_1, x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = lean_io_prim_handle_try_lock(x_8, x_11, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_io_prim_handle_unlock(x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_mk_string_unchecked("could not acquire an exclusive configuration lock; another process may already be reconfiguring the package", 107, 107);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_mk_string_unchecked("could not acquire an exclusive configuration lock; another process may already be reconfiguring the package", 107, 107);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_io_prim_handle_unlock(x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(3);
x_33 = lean_unbox(x_32);
x_34 = lean_io_prim_handle_mk(x_2, x_33, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unbox(x_10);
x_38 = lean_io_prim_handle_lock(x_35, x_37, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_io_prim_handle_unlock(x_8, x_39);
lean_dec(x_8);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_35);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_35);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_35);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_38);
if (x_49 == 0)
{
return x_38;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_38);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_dec(x_8);
return x_34;
}
}
else
{
uint8_t x_53; 
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_30);
if (x_53 == 0)
{
return x_30;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_30, 0);
x_55 = lean_ctor_get(x_30, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_30);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_8);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
return x_12;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_12, 0);
x_59 = lean_ctor_get(x_12, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_12);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__1(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_io_remove_file(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_System_Platform_target;
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = l_Lake_Env_leanGithash(x_14);
lean_dec(x_14);
x_16 = lean_box_uint64(x_3);
lean_inc(x_8);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_8);
x_18 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_896_(x_17);
x_19 = lean_unsigned_to_nat(80u);
x_20 = l_Lean_Json_pretty(x_18, x_19);
x_21 = l_IO_FS_Handle_putStrLn(x_7, x_20, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_io_prim_handle_truncate(x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_2, 9);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lake_elabConfigFile(x_4, x_8, x_25, x_5, x_9, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = l_Lean_writeModule(x_29, x_1, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_io_prim_handle_unlock(x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_27);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_27, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_io_error_to_string(x_42);
x_44 = lean_box(3);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = lean_array_get_size(x_30);
x_48 = lean_array_push(x_30, x_45);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_48);
lean_ctor_set(x_27, 0, x_47);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_27);
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
x_51 = lean_io_error_to_string(x_49);
x_52 = lean_box(3);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = lean_array_get_size(x_30);
x_56 = lean_array_push(x_30, x_53);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_56);
lean_ctor_set(x_27, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_27);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_27);
x_58 = lean_ctor_get(x_33, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_33, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_60 = x_33;
} else {
 lean_dec_ref(x_33);
 x_60 = lean_box(0);
}
x_61 = lean_io_error_to_string(x_58);
x_62 = lean_box(3);
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_unbox(x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_64);
x_65 = lean_array_get_size(x_30);
x_66 = lean_array_push(x_30, x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_60)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_60;
 lean_ctor_set_tag(x_68, 0);
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_27);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_27, 1);
lean_dec(x_70);
x_71 = lean_ctor_get(x_27, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_31);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_31, 0);
x_74 = lean_io_error_to_string(x_73);
x_75 = lean_box(3);
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
x_77 = lean_unbox(x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_77);
x_78 = lean_array_get_size(x_30);
x_79 = lean_array_push(x_30, x_76);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_79);
lean_ctor_set(x_27, 0, x_78);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_27);
return x_31;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_31, 0);
x_81 = lean_ctor_get(x_31, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_31);
x_82 = lean_io_error_to_string(x_80);
x_83 = lean_box(3);
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_85);
x_86 = lean_array_get_size(x_30);
x_87 = lean_array_push(x_30, x_84);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_87);
lean_ctor_set(x_27, 0, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_27);
lean_ctor_set(x_88, 1, x_81);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_27);
x_89 = lean_ctor_get(x_31, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_31, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_91 = x_31;
} else {
 lean_dec_ref(x_31);
 x_91 = lean_box(0);
}
x_92 = lean_io_error_to_string(x_89);
x_93 = lean_box(3);
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_unbox(x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_95);
x_96 = lean_array_get_size(x_30);
x_97 = lean_array_push(x_30, x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
if (lean_is_scalar(x_91)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_91;
 lean_ctor_set_tag(x_99, 0);
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_90);
return x_99;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_1);
return x_26;
}
}
else
{
uint8_t x_100; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_23);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_23, 0);
x_102 = lean_io_error_to_string(x_101);
x_103 = lean_box(3);
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_unbox(x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_105);
x_106 = lean_array_get_size(x_9);
x_107 = lean_array_push(x_9, x_104);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_108);
return x_23;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_109 = lean_ctor_get(x_23, 0);
x_110 = lean_ctor_get(x_23, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_23);
x_111 = lean_io_error_to_string(x_109);
x_112 = lean_box(3);
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
x_114 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_114);
x_115 = lean_array_get_size(x_9);
x_116 = lean_array_push(x_9, x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_110);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_21);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_21, 0);
x_121 = lean_io_error_to_string(x_120);
x_122 = lean_box(3);
x_123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_123, 0, x_121);
x_124 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_124);
x_125 = lean_array_get_size(x_9);
x_126 = lean_array_push(x_9, x_123);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_127);
return x_21;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_128 = lean_ctor_get(x_21, 0);
x_129 = lean_ctor_get(x_21, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_21);
x_130 = lean_io_error_to_string(x_128);
x_131 = lean_box(3);
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_unbox(x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_133);
x_134 = lean_array_get_size(x_9);
x_135 = lean_array_push(x_9, x_132);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_129);
return x_137;
}
}
}
else
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_11, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 11)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_138);
x_139 = lean_ctor_get(x_11, 1);
lean_inc(x_139);
lean_dec(x_11);
x_140 = l_System_Platform_target;
x_141 = lean_ctor_get(x_2, 0);
lean_inc(x_141);
x_142 = l_Lake_Env_leanGithash(x_141);
lean_dec(x_141);
x_143 = lean_box_uint64(x_3);
lean_inc(x_8);
x_144 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_8);
x_145 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_896_(x_144);
x_146 = lean_unsigned_to_nat(80u);
x_147 = l_Lean_Json_pretty(x_145, x_146);
x_148 = l_IO_FS_Handle_putStrLn(x_7, x_147, x_139);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_io_prim_handle_truncate(x_7, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_ctor_get(x_2, 9);
lean_inc(x_152);
lean_dec(x_2);
x_153 = l_Lake_elabConfigFile(x_4, x_8, x_152, x_5, x_9, x_151);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
x_158 = l_Lean_writeModule(x_156, x_1, x_155);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_io_prim_handle_unlock(x_7, x_159);
if (lean_obj_tag(x_160) == 0)
{
uint8_t x_161; 
lean_dec(x_157);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_160, 0);
lean_dec(x_162);
lean_ctor_set(x_160, 0, x_154);
return x_160;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_154);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_154);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_154, 1);
lean_dec(x_166);
x_167 = lean_ctor_get(x_154, 0);
lean_dec(x_167);
x_168 = !lean_is_exclusive(x_160);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_160, 0);
x_170 = lean_io_error_to_string(x_169);
x_171 = lean_box(3);
x_172 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_172, 0, x_170);
x_173 = lean_unbox(x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_173);
x_174 = lean_array_get_size(x_157);
x_175 = lean_array_push(x_157, x_172);
lean_ctor_set_tag(x_154, 1);
lean_ctor_set(x_154, 1, x_175);
lean_ctor_set(x_154, 0, x_174);
lean_ctor_set_tag(x_160, 0);
lean_ctor_set(x_160, 0, x_154);
return x_160;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_176 = lean_ctor_get(x_160, 0);
x_177 = lean_ctor_get(x_160, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_160);
x_178 = lean_io_error_to_string(x_176);
x_179 = lean_box(3);
x_180 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_180, 0, x_178);
x_181 = lean_unbox(x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_181);
x_182 = lean_array_get_size(x_157);
x_183 = lean_array_push(x_157, x_180);
lean_ctor_set_tag(x_154, 1);
lean_ctor_set(x_154, 1, x_183);
lean_ctor_set(x_154, 0, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_154);
lean_ctor_set(x_184, 1, x_177);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_154);
x_185 = lean_ctor_get(x_160, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_160, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_187 = x_160;
} else {
 lean_dec_ref(x_160);
 x_187 = lean_box(0);
}
x_188 = lean_io_error_to_string(x_185);
x_189 = lean_box(3);
x_190 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_190, 0, x_188);
x_191 = lean_unbox(x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*1, x_191);
x_192 = lean_array_get_size(x_157);
x_193 = lean_array_push(x_157, x_190);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
if (lean_is_scalar(x_187)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_187;
 lean_ctor_set_tag(x_195, 0);
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_186);
return x_195;
}
}
}
else
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_154);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = lean_ctor_get(x_154, 1);
lean_dec(x_197);
x_198 = lean_ctor_get(x_154, 0);
lean_dec(x_198);
x_199 = !lean_is_exclusive(x_158);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
x_200 = lean_ctor_get(x_158, 0);
x_201 = lean_io_error_to_string(x_200);
x_202 = lean_box(3);
x_203 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_203, 0, x_201);
x_204 = lean_unbox(x_202);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_204);
x_205 = lean_array_get_size(x_157);
x_206 = lean_array_push(x_157, x_203);
lean_ctor_set_tag(x_154, 1);
lean_ctor_set(x_154, 1, x_206);
lean_ctor_set(x_154, 0, x_205);
lean_ctor_set_tag(x_158, 0);
lean_ctor_set(x_158, 0, x_154);
return x_158;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_207 = lean_ctor_get(x_158, 0);
x_208 = lean_ctor_get(x_158, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_158);
x_209 = lean_io_error_to_string(x_207);
x_210 = lean_box(3);
x_211 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_211, 0, x_209);
x_212 = lean_unbox(x_210);
lean_ctor_set_uint8(x_211, sizeof(void*)*1, x_212);
x_213 = lean_array_get_size(x_157);
x_214 = lean_array_push(x_157, x_211);
lean_ctor_set_tag(x_154, 1);
lean_ctor_set(x_154, 1, x_214);
lean_ctor_set(x_154, 0, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_154);
lean_ctor_set(x_215, 1, x_208);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_154);
x_216 = lean_ctor_get(x_158, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_158, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_218 = x_158;
} else {
 lean_dec_ref(x_158);
 x_218 = lean_box(0);
}
x_219 = lean_io_error_to_string(x_216);
x_220 = lean_box(3);
x_221 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_221, 0, x_219);
x_222 = lean_unbox(x_220);
lean_ctor_set_uint8(x_221, sizeof(void*)*1, x_222);
x_223 = lean_array_get_size(x_157);
x_224 = lean_array_push(x_157, x_221);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
if (lean_is_scalar(x_218)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_218;
 lean_ctor_set_tag(x_226, 0);
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_217);
return x_226;
}
}
}
else
{
lean_dec(x_154);
lean_dec(x_1);
return x_153;
}
}
else
{
uint8_t x_227; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_150);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_150, 0);
x_229 = lean_io_error_to_string(x_228);
x_230 = lean_box(3);
x_231 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_231, 0, x_229);
x_232 = lean_unbox(x_230);
lean_ctor_set_uint8(x_231, sizeof(void*)*1, x_232);
x_233 = lean_array_get_size(x_9);
x_234 = lean_array_push(x_9, x_231);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set_tag(x_150, 0);
lean_ctor_set(x_150, 0, x_235);
return x_150;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_236 = lean_ctor_get(x_150, 0);
x_237 = lean_ctor_get(x_150, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_150);
x_238 = lean_io_error_to_string(x_236);
x_239 = lean_box(3);
x_240 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_240, 0, x_238);
x_241 = lean_unbox(x_239);
lean_ctor_set_uint8(x_240, sizeof(void*)*1, x_241);
x_242 = lean_array_get_size(x_9);
x_243 = lean_array_push(x_9, x_240);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_237);
return x_245;
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_148);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_247 = lean_ctor_get(x_148, 0);
x_248 = lean_io_error_to_string(x_247);
x_249 = lean_box(3);
x_250 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_250, 0, x_248);
x_251 = lean_unbox(x_249);
lean_ctor_set_uint8(x_250, sizeof(void*)*1, x_251);
x_252 = lean_array_get_size(x_9);
x_253 = lean_array_push(x_9, x_250);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set_tag(x_148, 0);
lean_ctor_set(x_148, 0, x_254);
return x_148;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_255 = lean_ctor_get(x_148, 0);
x_256 = lean_ctor_get(x_148, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_148);
x_257 = lean_io_error_to_string(x_255);
x_258 = lean_box(3);
x_259 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_259, 0, x_257);
x_260 = lean_unbox(x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_260);
x_261 = lean_array_get_size(x_9);
x_262 = lean_array_push(x_9, x_259);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_256);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_277; lean_object* x_278; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_265 = lean_ctor_get(x_11, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_266 = x_11;
} else {
 lean_dec_ref(x_11);
 x_266 = lean_box(0);
}
x_267 = lean_io_error_to_string(x_138);
x_268 = lean_box(3);
x_269 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_269, 0, x_267);
x_270 = lean_unbox(x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*1, x_270);
x_271 = lean_array_get_size(x_9);
x_277 = lean_array_push(x_9, x_269);
x_278 = lean_io_prim_handle_unlock(x_7, x_265);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_280 = lean_io_remove_file(x_6, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_272 = x_277;
x_273 = x_281;
goto block_276;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = lean_io_error_to_string(x_282);
x_285 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_285, 0, x_284);
x_286 = lean_unbox(x_268);
lean_ctor_set_uint8(x_285, sizeof(void*)*1, x_286);
x_287 = lean_array_push(x_277, x_285);
x_272 = x_287;
x_273 = x_283;
goto block_276;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; 
x_288 = lean_ctor_get(x_278, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_278, 1);
lean_inc(x_289);
lean_dec(x_278);
x_290 = lean_io_error_to_string(x_288);
x_291 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_unbox(x_268);
lean_ctor_set_uint8(x_291, sizeof(void*)*1, x_292);
x_293 = lean_array_push(x_277, x_291);
x_272 = x_293;
x_273 = x_289;
goto block_276;
}
block_276:
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
if (lean_is_scalar(x_266)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_266;
 lean_ctor_set_tag(x_275, 0);
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 6);
lean_inc(x_15);
lean_inc(x_15);
x_16 = l_System_FilePath_fileName(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_1);
x_17 = lean_mk_string_unchecked("invalid configuration file name", 31, 31);
x_18 = lean_box(3);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = lean_array_get_size(x_2);
x_22 = lean_array_push(x_2, x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_mk_string_unchecked("olean.lock", 10, 10);
x_27 = l_Lake_computeTextFileHash(x_15, x_3);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_256; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lake_defaultLakeDir;
x_31 = lean_mk_string_unchecked("olean", 5, 5);
x_32 = lean_mk_string_unchecked("olean.trace", 11, 11);
lean_inc(x_25);
x_33 = l_System_FilePath_withExtension(x_25, x_26);
lean_dec(x_26);
x_34 = lean_ctor_get(x_1, 4);
lean_inc(x_34);
lean_inc(x_34);
x_35 = l_Lake_joinRelative(x_34, x_30);
lean_inc(x_25);
x_36 = l_System_FilePath_withExtension(x_25, x_31);
lean_dec(x_31);
x_37 = l_System_FilePath_withExtension(x_25, x_32);
lean_dec(x_32);
lean_inc(x_35);
x_38 = l_Lake_joinRelative(x_35, x_33);
lean_dec(x_33);
lean_inc(x_35);
x_39 = l_Lake_joinRelative(x_35, x_37);
lean_dec(x_37);
x_40 = l_System_FilePath_pathExists(x_39, x_29);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
lean_inc(x_35);
x_44 = l_Lake_joinRelative(x_35, x_36);
lean_dec(x_36);
x_256 = lean_unbox(x_41);
lean_dec(x_41);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = l_IO_FS_createDirAll(x_35, x_42);
lean_dec(x_35);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_259 = lean_box(2);
x_260 = lean_unbox(x_259);
x_261 = lean_io_prim_handle_mk(x_39, x_260, x_258);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; 
lean_dec(x_43);
lean_dec(x_38);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_box(1);
x_265 = lean_unbox(x_264);
x_266 = lean_io_prim_handle_lock(x_262, x_265, x_263);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; uint64_t x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = lean_ctor_get(x_1, 8);
lean_inc(x_268);
x_269 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_270 = l_Lake_importConfigFile___lam__1(x_44, x_1, x_269, x_34, x_15, x_39, x_262, x_268, x_2, x_267);
lean_dec(x_262);
lean_dec(x_39);
return x_270;
}
else
{
uint8_t x_271; 
lean_dec(x_262);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_266);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_272 = lean_ctor_get(x_266, 0);
x_273 = lean_io_error_to_string(x_272);
x_274 = lean_box(3);
x_275 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_275, 0, x_273);
x_276 = lean_unbox(x_274);
lean_ctor_set_uint8(x_275, sizeof(void*)*1, x_276);
x_277 = lean_array_get_size(x_2);
x_278 = lean_array_push(x_2, x_275);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
lean_ctor_set_tag(x_266, 0);
lean_ctor_set(x_266, 0, x_279);
return x_266;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_280 = lean_ctor_get(x_266, 0);
x_281 = lean_ctor_get(x_266, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_266);
x_282 = lean_io_error_to_string(x_280);
x_283 = lean_box(3);
x_284 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_284, 0, x_282);
x_285 = lean_unbox(x_283);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_285);
x_286 = lean_array_get_size(x_2);
x_287 = lean_array_push(x_2, x_284);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_281);
return x_289;
}
}
}
else
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_261, 0);
lean_inc(x_290);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; 
lean_dec(x_290);
x_291 = lean_ctor_get(x_261, 1);
lean_inc(x_291);
lean_dec(x_261);
x_292 = lean_box(0);
x_293 = lean_unbox(x_292);
x_294 = lean_io_prim_handle_mk(x_39, x_293, x_291);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_75 = x_295;
x_76 = x_2;
x_77 = x_296;
goto block_255;
}
else
{
uint8_t x_297; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_294);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_298 = lean_ctor_get(x_294, 0);
x_299 = lean_io_error_to_string(x_298);
x_300 = lean_box(3);
x_301 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_301, 0, x_299);
x_302 = lean_unbox(x_300);
lean_ctor_set_uint8(x_301, sizeof(void*)*1, x_302);
x_303 = lean_array_get_size(x_2);
x_304 = lean_array_push(x_2, x_301);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
lean_ctor_set_tag(x_294, 0);
lean_ctor_set(x_294, 0, x_305);
return x_294;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_306 = lean_ctor_get(x_294, 0);
x_307 = lean_ctor_get(x_294, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_294);
x_308 = lean_io_error_to_string(x_306);
x_309 = lean_box(3);
x_310 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_310, 0, x_308);
x_311 = lean_unbox(x_309);
lean_ctor_set_uint8(x_310, sizeof(void*)*1, x_311);
x_312 = lean_array_get_size(x_2);
x_313 = lean_array_push(x_2, x_310);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_307);
return x_315;
}
}
}
else
{
uint8_t x_316; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_316 = !lean_is_exclusive(x_261);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_317 = lean_ctor_get(x_261, 0);
lean_dec(x_317);
x_318 = lean_io_error_to_string(x_290);
x_319 = lean_box(3);
x_320 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_320, 0, x_318);
x_321 = lean_unbox(x_319);
lean_ctor_set_uint8(x_320, sizeof(void*)*1, x_321);
x_322 = lean_array_get_size(x_2);
x_323 = lean_array_push(x_2, x_320);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
lean_ctor_set_tag(x_261, 0);
lean_ctor_set(x_261, 0, x_324);
return x_261;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_325 = lean_ctor_get(x_261, 1);
lean_inc(x_325);
lean_dec(x_261);
x_326 = lean_io_error_to_string(x_290);
x_327 = lean_box(3);
x_328 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_328, 0, x_326);
x_329 = lean_unbox(x_327);
lean_ctor_set_uint8(x_328, sizeof(void*)*1, x_329);
x_330 = lean_array_get_size(x_2);
x_331 = lean_array_push(x_2, x_328);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_325);
return x_333;
}
}
}
}
else
{
uint8_t x_334; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_334 = !lean_is_exclusive(x_257);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_335 = lean_ctor_get(x_257, 0);
x_336 = lean_io_error_to_string(x_335);
x_337 = lean_box(3);
x_338 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_338, 0, x_336);
x_339 = lean_unbox(x_337);
lean_ctor_set_uint8(x_338, sizeof(void*)*1, x_339);
x_340 = lean_array_get_size(x_2);
x_341 = lean_array_push(x_2, x_338);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
lean_ctor_set_tag(x_257, 0);
lean_ctor_set(x_257, 0, x_342);
return x_257;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_343 = lean_ctor_get(x_257, 0);
x_344 = lean_ctor_get(x_257, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_257);
x_345 = lean_io_error_to_string(x_343);
x_346 = lean_box(3);
x_347 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_347, 0, x_345);
x_348 = lean_unbox(x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*1, x_348);
x_349 = lean_array_get_size(x_2);
x_350 = lean_array_push(x_2, x_347);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_344);
return x_352;
}
}
}
else
{
lean_object* x_353; uint8_t x_354; lean_object* x_355; 
lean_dec(x_35);
x_353 = lean_box(0);
x_354 = lean_unbox(x_353);
x_355 = lean_io_prim_handle_mk(x_39, x_354, x_42);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_75 = x_356;
x_76 = x_2;
x_77 = x_357;
goto block_255;
}
else
{
uint8_t x_358; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_358 = !lean_is_exclusive(x_355);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_359 = lean_ctor_get(x_355, 0);
x_360 = lean_io_error_to_string(x_359);
x_361 = lean_box(3);
x_362 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_362, 0, x_360);
x_363 = lean_unbox(x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*1, x_363);
x_364 = lean_array_get_size(x_2);
x_365 = lean_array_push(x_2, x_362);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set_tag(x_355, 0);
lean_ctor_set(x_355, 0, x_366);
return x_355;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_367 = lean_ctor_get(x_355, 0);
x_368 = lean_ctor_get(x_355, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_355);
x_369 = lean_io_error_to_string(x_367);
x_370 = lean_box(3);
x_371 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_371, 0, x_369);
x_372 = lean_unbox(x_370);
lean_ctor_set_uint8(x_371, sizeof(void*)*1, x_372);
x_373 = lean_array_get_size(x_2);
x_374 = lean_array_push(x_2, x_371);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_368);
return x_376;
}
}
}
block_74:
{
lean_object* x_49; 
x_49 = l_Lake_importConfigFile___lam__0(x_38, x_39, x_47, x_46);
lean_dec(x_47);
lean_dec(x_38);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; 
lean_dec(x_43);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_48, 3);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_54 = l_Lake_importConfigFile___lam__1(x_44, x_1, x_53, x_34, x_15, x_39, x_50, x_52, x_45, x_51);
lean_dec(x_50);
lean_dec(x_39);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_49);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = lean_io_error_to_string(x_56);
x_58 = lean_box(3);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_unbox(x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
x_61 = lean_array_get_size(x_45);
x_62 = lean_array_push(x_45, x_59);
if (lean_is_scalar(x_43)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_43;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_tag(x_49, 0);
lean_ctor_set(x_49, 0, x_63);
return x_49;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_49, 0);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_49);
x_66 = lean_io_error_to_string(x_64);
x_67 = lean_box(3);
x_68 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_68, 0, x_66);
x_69 = lean_unbox(x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_69);
x_70 = lean_array_get_size(x_45);
x_71 = lean_array_push(x_45, x_68);
if (lean_is_scalar(x_43)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_43;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
return x_73;
}
}
}
block_255:
{
uint8_t x_78; 
x_78 = lean_ctor_get_uint8(x_1, sizeof(void*)*12);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_io_prim_handle_lock(x_75, x_78, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_IO_FS_Handle_readToEnd(x_75, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Json_parse(x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_dec(x_84);
lean_dec(x_75);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_4 = x_76;
x_5 = x_83;
goto block_14;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_976_(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_dec(x_86);
lean_dec(x_75);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_4 = x_76;
x_5 = x_83;
goto block_14;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_System_FilePath_pathExists(x_44, x_83);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_45 = x_76;
x_46 = x_91;
x_47 = x_75;
x_48 = x_87;
goto block_74;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_88, 1);
x_94 = lean_ctor_get(x_88, 0);
lean_dec(x_94);
x_95 = lean_ctor_get(x_87, 0);
lean_inc(x_95);
x_96 = l_System_Platform_target;
x_97 = lean_string_dec_eq(x_95, x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_free_object(x_88);
x_45 = x_76;
x_46 = x_93;
x_47 = x_75;
x_48 = x_87;
goto block_74;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 0);
lean_inc(x_99);
x_100 = l_Lake_Env_leanGithash(x_99);
lean_dec(x_99);
x_101 = lean_string_dec_eq(x_98, x_100);
lean_dec(x_100);
lean_dec(x_98);
if (x_101 == 0)
{
lean_free_object(x_88);
x_45 = x_76;
x_46 = x_93;
x_47 = x_75;
x_48 = x_87;
goto block_74;
}
else
{
lean_object* x_102; uint64_t x_103; uint64_t x_104; uint8_t x_105; 
x_102 = lean_ctor_get(x_87, 2);
lean_inc(x_102);
x_103 = lean_unbox_uint64(x_102);
lean_dec(x_102);
x_104 = lean_unbox_uint64(x_28);
x_105 = lean_uint64_dec_eq(x_103, x_104);
if (x_105 == 0)
{
lean_free_object(x_88);
x_45 = x_76;
x_46 = x_93;
x_47 = x_75;
x_48 = x_87;
goto block_74;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_87);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
x_106 = lean_ctor_get(x_1, 9);
lean_inc(x_106);
lean_dec(x_1);
x_107 = l_Lake_importConfigFileCore(x_44, x_106, x_93);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_io_prim_handle_unlock(x_75, x_109);
lean_dec(x_75);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
lean_ctor_set(x_88, 1, x_76);
lean_ctor_set(x_88, 0, x_108);
lean_ctor_set(x_110, 0, x_88);
return x_110;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
lean_ctor_set(x_88, 1, x_76);
lean_ctor_set(x_88, 0, x_108);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_88);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_108);
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_110, 0);
x_117 = lean_io_error_to_string(x_116);
x_118 = lean_box(3);
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
x_120 = lean_unbox(x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_120);
x_121 = lean_array_get_size(x_76);
x_122 = lean_array_push(x_76, x_119);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 1, x_122);
lean_ctor_set(x_88, 0, x_121);
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 0, x_88);
return x_110;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_123 = lean_ctor_get(x_110, 0);
x_124 = lean_ctor_get(x_110, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_110);
x_125 = lean_io_error_to_string(x_123);
x_126 = lean_box(3);
x_127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_127, 0, x_125);
x_128 = lean_unbox(x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_128);
x_129 = lean_array_get_size(x_76);
x_130 = lean_array_push(x_76, x_127);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 1, x_130);
lean_ctor_set(x_88, 0, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_88);
lean_ctor_set(x_131, 1, x_124);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_75);
x_132 = !lean_is_exclusive(x_107);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; 
x_133 = lean_ctor_get(x_107, 0);
x_134 = lean_io_error_to_string(x_133);
x_135 = lean_box(3);
x_136 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_136, 0, x_134);
x_137 = lean_unbox(x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_137);
x_138 = lean_array_get_size(x_76);
x_139 = lean_array_push(x_76, x_136);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 1, x_139);
lean_ctor_set(x_88, 0, x_138);
lean_ctor_set_tag(x_107, 0);
lean_ctor_set(x_107, 0, x_88);
return x_107;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_140 = lean_ctor_get(x_107, 0);
x_141 = lean_ctor_get(x_107, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_107);
x_142 = lean_io_error_to_string(x_140);
x_143 = lean_box(3);
x_144 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_144, 0, x_142);
x_145 = lean_unbox(x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_145);
x_146 = lean_array_get_size(x_76);
x_147 = lean_array_push(x_76, x_144);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 1, x_147);
lean_ctor_set(x_88, 0, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_88);
lean_ctor_set(x_148, 1, x_141);
return x_148;
}
}
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_88, 1);
lean_inc(x_149);
lean_dec(x_88);
x_150 = lean_ctor_get(x_87, 0);
lean_inc(x_150);
x_151 = l_System_Platform_target;
x_152 = lean_string_dec_eq(x_150, x_151);
lean_dec(x_150);
if (x_152 == 0)
{
x_45 = x_76;
x_46 = x_149;
x_47 = x_75;
x_48 = x_87;
goto block_74;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_153 = lean_ctor_get(x_87, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_1, 0);
lean_inc(x_154);
x_155 = l_Lake_Env_leanGithash(x_154);
lean_dec(x_154);
x_156 = lean_string_dec_eq(x_153, x_155);
lean_dec(x_155);
lean_dec(x_153);
if (x_156 == 0)
{
x_45 = x_76;
x_46 = x_149;
x_47 = x_75;
x_48 = x_87;
goto block_74;
}
else
{
lean_object* x_157; uint64_t x_158; uint64_t x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_87, 2);
lean_inc(x_157);
x_158 = lean_unbox_uint64(x_157);
lean_dec(x_157);
x_159 = lean_unbox_uint64(x_28);
x_160 = lean_uint64_dec_eq(x_158, x_159);
if (x_160 == 0)
{
x_45 = x_76;
x_46 = x_149;
x_47 = x_75;
x_48 = x_87;
goto block_74;
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_87);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
x_161 = lean_ctor_get(x_1, 9);
lean_inc(x_161);
lean_dec(x_1);
x_162 = l_Lake_importConfigFileCore(x_44, x_161, x_149);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_io_prim_handle_unlock(x_75, x_164);
lean_dec(x_75);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_76);
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_163);
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_165, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_172 = x_165;
} else {
 lean_dec_ref(x_165);
 x_172 = lean_box(0);
}
x_173 = lean_io_error_to_string(x_170);
x_174 = lean_box(3);
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
x_176 = lean_unbox(x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_176);
x_177 = lean_array_get_size(x_76);
x_178 = lean_array_push(x_76, x_175);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
if (lean_is_scalar(x_172)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_172;
 lean_ctor_set_tag(x_180, 0);
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_171);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_75);
x_181 = lean_ctor_get(x_162, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_162, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_183 = x_162;
} else {
 lean_dec_ref(x_162);
 x_183 = lean_box(0);
}
x_184 = lean_io_error_to_string(x_181);
x_185 = lean_box(3);
x_186 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_186, 0, x_184);
x_187 = lean_unbox(x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_187);
x_188 = lean_array_get_size(x_76);
x_189 = lean_array_push(x_76, x_186);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
if (lean_is_scalar(x_183)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_183;
 lean_ctor_set_tag(x_191, 0);
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_182);
return x_191;
}
}
}
}
}
}
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_75);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_81);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_193 = lean_ctor_get(x_81, 0);
x_194 = lean_io_error_to_string(x_193);
x_195 = lean_box(3);
x_196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_196, 0, x_194);
x_197 = lean_unbox(x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_197);
x_198 = lean_array_get_size(x_76);
x_199 = lean_array_push(x_76, x_196);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set_tag(x_81, 0);
lean_ctor_set(x_81, 0, x_200);
return x_81;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_201 = lean_ctor_get(x_81, 0);
x_202 = lean_ctor_get(x_81, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_81);
x_203 = lean_io_error_to_string(x_201);
x_204 = lean_box(3);
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
x_206 = lean_unbox(x_204);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_206);
x_207 = lean_array_get_size(x_76);
x_208 = lean_array_push(x_76, x_205);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_202);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_75);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_79);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_212 = lean_ctor_get(x_79, 0);
x_213 = lean_io_error_to_string(x_212);
x_214 = lean_box(3);
x_215 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_215, 0, x_213);
x_216 = lean_unbox(x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_216);
x_217 = lean_array_get_size(x_76);
x_218 = lean_array_push(x_76, x_215);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set_tag(x_79, 0);
lean_ctor_set(x_79, 0, x_219);
return x_79;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_220 = lean_ctor_get(x_79, 0);
x_221 = lean_ctor_get(x_79, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_79);
x_222 = lean_io_error_to_string(x_220);
x_223 = lean_box(3);
x_224 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_224, 0, x_222);
x_225 = lean_unbox(x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_225);
x_226 = lean_array_get_size(x_76);
x_227 = lean_array_push(x_76, x_224);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_221);
return x_229;
}
}
}
else
{
lean_object* x_230; 
lean_dec(x_43);
x_230 = l_Lake_importConfigFile___lam__0(x_38, x_39, x_75, x_77);
lean_dec(x_75);
lean_dec(x_38);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint64_t x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_1, 8);
lean_inc(x_233);
x_234 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_235 = l_Lake_importConfigFile___lam__1(x_44, x_1, x_234, x_34, x_15, x_39, x_231, x_233, x_76, x_232);
lean_dec(x_231);
lean_dec(x_39);
return x_235;
}
else
{
uint8_t x_236; 
lean_dec(x_44);
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_230);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_237 = lean_ctor_get(x_230, 0);
x_238 = lean_io_error_to_string(x_237);
x_239 = lean_box(3);
x_240 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_240, 0, x_238);
x_241 = lean_unbox(x_239);
lean_ctor_set_uint8(x_240, sizeof(void*)*1, x_241);
x_242 = lean_array_get_size(x_76);
x_243 = lean_array_push(x_76, x_240);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set_tag(x_230, 0);
lean_ctor_set(x_230, 0, x_244);
return x_230;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_245 = lean_ctor_get(x_230, 0);
x_246 = lean_ctor_get(x_230, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_230);
x_247 = lean_io_error_to_string(x_245);
x_248 = lean_box(3);
x_249 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_249, 0, x_247);
x_250 = lean_unbox(x_248);
lean_ctor_set_uint8(x_249, sizeof(void*)*1, x_250);
x_251 = lean_array_get_size(x_76);
x_252 = lean_array_push(x_76, x_249);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_246);
return x_254;
}
}
}
}
}
else
{
uint8_t x_377; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_1);
x_377 = !lean_is_exclusive(x_27);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_378 = lean_ctor_get(x_27, 0);
x_379 = lean_io_error_to_string(x_378);
x_380 = lean_box(3);
x_381 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_381, 0, x_379);
x_382 = lean_unbox(x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*1, x_382);
x_383 = lean_array_get_size(x_2);
x_384 = lean_array_push(x_2, x_381);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_385);
return x_27;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_386 = lean_ctor_get(x_27, 0);
x_387 = lean_ctor_get(x_27, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_27);
x_388 = lean_io_error_to_string(x_386);
x_389 = lean_box(3);
x_390 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_390, 0, x_388);
x_391 = lean_unbox(x_389);
lean_ctor_set_uint8(x_390, sizeof(void*)*1, x_391);
x_392 = lean_array_get_size(x_2);
x_393 = lean_array_push(x_2, x_390);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_387);
return x_395;
}
}
}
block_14:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_mk_string_unchecked("compiled configuration is invalid; run with '-R' to reconfigure", 63, 63);
x_7 = lean_box(3);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_array_get_size(x_4);
x_11 = lean_array_push(x_4, x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_importConfigFile___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; lean_object* x_12; 
x_11 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_12 = l_Lake_importConfigFile___lam__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Extensions(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Frontend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Extensions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instBEqImport__lake = _init_l_Lake_instBEqImport__lake();
lean_mark_persistent(l_Lake_instBEqImport__lake);
l_Lake_instHashableImport__lake = _init_l_Lake_instHashableImport__lake();
lean_mark_persistent(l_Lake_instHashableImport__lake);
if (builtin) {res = l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_146_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lake_importEnvCache = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_importEnvCache);
lean_dec_ref(res);
}l_Lake_configModuleName = _init_l_Lake_configModuleName();
lean_mark_persistent(l_Lake_configModuleName);
l_Lake_importConfigFileCore_lakeExts = _init_l_Lake_importConfigFileCore_lakeExts();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts);
l_Lake_instToJsonConfigTrace = _init_l_Lake_instToJsonConfigTrace();
lean_mark_persistent(l_Lake_instToJsonConfigTrace);
l_Lake_instFromJsonConfigTrace = _init_l_Lake_instFromJsonConfigTrace();
lean_mark_persistent(l_Lake_instFromJsonConfigTrace);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
