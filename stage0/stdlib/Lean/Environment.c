// Lean compiler output
// Module: Lean.Environment
// Imports: Init.Control.StateRef Init.Data.Array.BinSearch Init.Data.Stream Init.System.Promise Lean.ImportingFlag Lean.Data.NameTrie Lean.Data.SMap Lean.Setup Lean.Declaration Lean.LocalContext Lean.Util.Path Lean.Util.FindExpr Lean.Util.Profile Lean.Util.InstantiateLevelParams Lean.Util.FoldConsts Lean.PrivateName Lean.LoadDynlib Init.Dynamic
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
uint8_t lean_compacted_region_is_memory_mapped(size_t);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_mkModuleData_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadEnvOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Environment_replayConsts_replayKernel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncConstantInfo_isUnsafe___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImportModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addExtraName___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findAsyncCore_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_readModuleData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleData(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_elab_environment_of_kernel_env(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_finalizeImport_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_header___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_evalConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_Diagnostics_isEnabled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_mkInitialExtStates(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_enableRealizationsForConst___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lean_kernel_set_diag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedModuleData;
LEAN_EXPORT lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_hasUnsafe___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___lam__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedVisibilityMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_enableDiag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Environment_realizeConst_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_allImportedModuleNames___boxed(lean_object*);
lean_object* lean_io_promise_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension_unsafe__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_writeModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_save_module_data_parts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Environment_replayConsts_replayKernel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_finalizeImport_unsafe__3___boxed(lean_object*);
lean_object* l_instToStringNat___lam__0(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_subsumesInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprConstantKind;
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtensionState;
LEAN_EXPORT lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_saveModuleDataParts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__9_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__2(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_enableRealizationsForConst_unsafe__1___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_kernel_is_def_eq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Environment_realizeConst_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_isRealizing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkExtNameMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_subsumesInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_findOLeanParts___lam__0(uint8_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_elab_environment_to_kernel_env(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts_replayKernel_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_publicModule_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_unlockAsync___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* lean_get_num_attributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAsyncConsts;
LEAN_EXPORT lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_importEnv_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_findOLeanParts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_finalizeImport_unsafe__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Environment_replayConsts_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_imports___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts_replayKernel_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Environment_dbgFormatCheckedSyncState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_AsyncContext_mayContain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_enterAsync(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_getDiagnostics(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportStateM_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_looksLikeOldCodegenName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_finalizeImport_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_kernel_check(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_findStateAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_enableDiag___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_mkInitialExtensionStates(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addExtraName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionEntrySpec;
LEAN_EXPORT lean_object* l_Lean_Environment_setExporting___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___redArg(uint8_t, uint8_t);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtensionDescr_name___autoParam;
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_EnvExtension_mkInitialExtStates_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_containsOnBranch___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addDeclCore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_writeModule___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtension___lam__0(lean_object*);
lean_object* lean_read_module_data_parts(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtension(lean_object*);
lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_finalizeImport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Environment_0__Lean_EnvExtension_setStateImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___at_____private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___at_____private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Format_isNil(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Kernel_Environment_isQuotInit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__3(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_finalizeImport_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_elab_environment_update_base_after_kernel_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAlreadyImported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11_spec__11(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_get_stdout(lean_object*);
lean_object* l_Lean_withImporting___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
lean_object* lean_elab_add_decl_without_checking(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_isReservedName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_environment_mark_quot_init(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Environment_displayStats_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_envExtensionsRef;
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Environment_realizeConst_spec__4(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension_unsafe__1___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleData___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__4(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_debug_skipKernelTC;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3_spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleData___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_findTask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_addDeclWithoutChecking___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_toCtorIdx___boxed(lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModulesCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_isResolved___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findRec_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_publicModule_x3f(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_isImportedConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_set_heartbeats(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_enableRealizationsForConst___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_hasUnsafe___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAsyncConstantInfo;
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__0(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncContext_mayContain___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkEmptyEnvironment___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instModuleIdxBEq;
LEAN_EXPORT lean_object* l_Lean_ConstantKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__0(lean_object*, uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_isDiagnosticsEnabled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedVisibilityMap(lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_resetDiag(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instModuleIdxToString;
LEAN_EXPORT uint8_t l_Lean_AsyncConstantInfo_isUnsafe(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_displayStats(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Kernel_Environment_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_foldl___at_____private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_dbgFormatAsyncState_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11___boxed(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_asyncMayContain(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0(uint8_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_isSafeDefinition___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_importModulesCore_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_importEnv_x3f_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_mkModuleData_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtensionState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAlreadyImported___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__0(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_mkPtrSet(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedConstantKind;
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_environment_quot_init(lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NamePart_cmp___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_addDeclCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_freeRegions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_looksLikeOldCodegenName___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_enterAsyncRealizing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_setCheckedSync___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Declaration_getNames(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst_unsafe__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo_spec__0(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantKind_ofConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__2(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Environment_displayStats_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_adjustFileName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElemArrayModuleIdxLtNatToNatSize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportStateM_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAlreadyImported___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_setDiagnostics(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_update_env_attributes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_ensureExtensionsArraySize_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_findTask(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_toCtorIdx___boxed(lean_object*);
lean_object* l_List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImportModules(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqOLeanLevel___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___Lean_Environment_displayStats_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Declaration_getTopLevelNames(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_enableDiag___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0(lean_object*);
uint8_t l_List_beq___at_____private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431__spec__0(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_dbgFormatAsyncState_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_empty(lean_object*);
LEAN_EXPORT uint8_t l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_isDefEqGuarded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at___Lean_Environment_displayStats_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadEnvOfMonadLift___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_readModuleData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_asyncConsts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_findConstVal_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_ensureExtensionsArraySize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElemArrayModuleIdxLtNatToNatSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_finalizeImport_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_finalizeImport_unsafe__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_anyMUnsafe_any___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_instInhabitedDiagnostics;
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_importModulesCore_go_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizingStack(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_hasUnsafe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_load_plugin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__1(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_OLeanLevel_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_AddConstAsyncResult_commitSignature(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_finalizeImport_spec__9(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_EnvExtension_mkInitialExtStates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lake_environment_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_mainModule___boxed(lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo;
lean_object* lean_elab_add_decl(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findAsyncCore_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__3(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_addDeclCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_promiseChecked___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_const___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedModuleIdx;
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_enableDiag___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_initFn____x40_Lean_Environment___hyg_6645_(lean_object*);
uint8_t l_Lean_SMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_isConstructor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Environment_replayConsts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_promiseChecked(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_isRealizing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_freeRegions_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_getMaxHeight___lam__0(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_promiseChecked___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts_replayKernel(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_hints(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_const2ModIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_findAsync_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230_(uint8_t, uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instTypeNameAsyncConsts;
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqConstantKind;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__0(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at___Lean_mkModuleData_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_mkModuleData_spec__4_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Kernel_isDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModules_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_EnvExtension_instInhabitedAsyncMode;
LEAN_EXPORT lean_object* l_Lean_Environment_enableRealizationsForConst_unsafe__1(lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_findStateAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtensionStateSpec;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_free___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_kernel_diag_is_enabled(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_whnf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl_without_checking(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_NameTrie_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11___boxed(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_persistentEnvExtensionsRef;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_6_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_imports(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleData___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModulesCore_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_mkModuleData_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_NameTrie_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_findStateAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImportModules___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withImportModules___redArg(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_importModulesCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleIdx_toNat(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Environment_0__Lean_AsyncConsts_add_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_readModuleDataParts___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Kernel_check___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_importModulesCore_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_8540_(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_resetDiag___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_lakeAdd___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdxFor_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_isDiagnosticsEnabled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_resetDiag___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_findStateAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_findOLeanParts___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_isMemoryMapped___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_resetDiag(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_EnvExtension_modifyState_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_writeModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_resetDiag___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_enterAsync___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts_replayKernel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_dbgFormatAsyncState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_invalidExtMsg;
LEAN_EXPORT lean_object* l_Lean_Environment_realizingStack___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_saveModuleData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_kernel_record_unfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_asyncConsts___boxed(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleData___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t l_Lean_NameMap_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___redArg___lam__0(lean_object*);
lean_object* lean_compacted_region_free(size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_runtime_mark_persistent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Environment_realizeConst_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_environment_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe_findRecExts_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_getModuleIdx_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_enterAsyncRealizing___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5___redArg(lean_object*);
lean_object* lean_kernel_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_setDiagnostics___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
LEAN_EXPORT lean_object* lean_kernel_get_diag(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule_unsafe__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_importModules_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AsyncConstantInfo_ofConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__4(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantKind_ofConstantInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_environment_free_regions(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instGetElemArrayModuleIdxLtNatToNatSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDeclWithoutChecking___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___redArg___lam__0(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_serverData_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_adjustFileName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_serverData_x3f(lean_object*, uint8_t);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_importModules_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_saveModuleData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at___Lean_mkModuleData_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_realizeConst_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_asyncMayContain___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleIdx_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAlreadyImported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_importModules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_mk_string_unchecked("debug", 5, 5);
x_3 = lean_mk_string_unchecked("skipKernelTC", 12, 12);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("skip kernel type checker. WARNING: setting this option to true may compromise soundness because your proofs will not be checked by the Lean kernel", 146, 146);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = l_Lean_Name_mkStr3(x_8, x_2, x_3);
x_10 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_7, x_9, x_1);
lean_dec(x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_EnvExtensionStateSpec() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, lean_box(0));
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedEnvExtensionState() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_EnvExtensionStateSpec;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_instModuleIdxBEq() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instModuleIdxToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringNat___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleIdx_toNat(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleIdx_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ModuleIdx_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedModuleIdx() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemArrayModuleIdxLtNatToNatSize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_fget(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemArrayModuleIdxLtNatToNatSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instGetElemArrayModuleIdxLtNatToNatSize___lam__0___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElemArrayModuleIdxLtNatToNatSize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instGetElemArrayModuleIdxLtNatToNatSize___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_get(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__0___boxed), 2, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__1___boxed), 3, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_instGetElemArrayModuleIdxLtNatToNatSize___lam__0___boxed), 3, 0);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instGetElem_x3fArrayModuleIdxLtNatToNatSize___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_isMemoryMapped___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_compacted_region_is_memory_mapped(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_CompactedRegion_free___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_compacted_region_free(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_EnvExtensionEntrySpec() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Lean_instInhabitedModuleData() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_box(0);
x_2 = l_Array_empty(lean_box(0));
lean_inc_n(x_2, 4);
x_3 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*5, x_4);
return x_3;
}
}
static lean_object* _init_l_Lean_Kernel_instInhabitedDiagnostics() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_5);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(5u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_shift_left(x_10, x_8);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get(x_6, x_5, x_14);
lean_dec(x_14);
lean_dec(x_5);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_name_eq(x_3, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_free_object(x_1);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_free_object(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_26 = lean_unsigned_to_nat(5u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_shift_left(x_29, x_27);
x_31 = lean_usize_sub(x_30, x_29);
x_32 = lean_usize_land(x_2, x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_array_get(x_25, x_24, x_33);
lean_dec(x_33);
lean_dec(x_24);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_name_eq(x_3, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
}
case 1:
{
lean_object* x_40; size_t x_41; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_usize_shift_right(x_2, x_27);
x_1 = x_40;
x_2 = x_41;
goto _start;
}
default: 
{
lean_object* x_43; 
x_43 = lean_box(0);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___redArg(x_44, x_45, x_46, x_3);
lean_dec(x_45);
lean_dec(x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
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
x_23 = lean_array_uget(x_6, x_22);
lean_dec(x_6);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_2, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_5, x_2);
return x_25;
}
else
{
lean_dec(x_5);
return x_24;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = l_Lean_Name_hash___override(x_2);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_27, x_43);
lean_dec(x_27);
x_45 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_2, x_44);
lean_dec(x_44);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_environment_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1_spec__1(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_environment_mark_quot_init(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_box(1);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
x_10 = lean_unbox(x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*6, x_10);
return x_9;
}
}
LEAN_EXPORT uint8_t lean_environment_quot_init(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Kernel_Environment_isQuotInit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_environment_quot_init(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDeclCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_add_decl(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDeclWithoutChecking___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_add_decl_without_checking(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_4 = l_Lean_Name_instBEq;
x_5 = l_Lean_instHashableName;
x_6 = l_Lean_Name_hash___override(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_9, x_2, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_array_get_size(x_16);
x_18 = l_Lean_Name_hash___override(x_2);
x_19 = lean_unsigned_to_nat(32u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_unsigned_to_nat(16u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_shift_right(x_22, x_24);
x_26 = lean_uint64_xor(x_22, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_usize_of_nat(x_29);
x_31 = lean_usize_sub(x_28, x_30);
x_32 = lean_usize_land(x_27, x_31);
x_33 = lean_array_uget(x_16, x_32);
x_34 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_nat_add(x_15, x_29);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_3);
lean_ctor_set(x_36, 2, x_33);
x_37 = lean_array_uset(x_16, x_32, x_36);
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
lean_object* x_44; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_37);
lean_ctor_set(x_13, 1, x_44);
lean_ctor_set(x_13, 0, x_35);
return x_1;
}
else
{
lean_ctor_set(x_13, 1, x_37);
lean_ctor_set(x_13, 0, x_35);
return x_1;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_box(0);
x_46 = lean_array_uset(x_16, x_32, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_2, x_3, x_33);
x_48 = lean_array_uset(x_46, x_32, x_47);
lean_ctor_set(x_13, 1, x_48);
return x_1;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; size_t x_61; size_t x_62; lean_object* x_63; size_t x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_array_get_size(x_50);
x_52 = l_Lean_Name_hash___override(x_2);
x_53 = lean_unsigned_to_nat(32u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_uint64_shift_right(x_52, x_54);
x_56 = lean_uint64_xor(x_52, x_55);
x_57 = lean_unsigned_to_nat(16u);
x_58 = lean_uint64_of_nat(x_57);
x_59 = lean_uint64_shift_right(x_56, x_58);
x_60 = lean_uint64_xor(x_56, x_59);
x_61 = lean_uint64_to_usize(x_60);
x_62 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_usize_of_nat(x_63);
x_65 = lean_usize_sub(x_62, x_64);
x_66 = lean_usize_land(x_61, x_65);
x_67 = lean_array_uget(x_50, x_66);
x_68 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_69 = lean_nat_add(x_49, x_63);
lean_dec(x_49);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_3);
lean_ctor_set(x_70, 2, x_67);
x_71 = lean_array_uset(x_50, x_66, x_70);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_nat_shiftl(x_69, x_72);
x_74 = lean_unsigned_to_nat(3u);
x_75 = lean_nat_div(x_73, x_74);
lean_dec(x_73);
x_76 = lean_array_get_size(x_71);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_71);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_1, 0, x_79);
return x_1;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_1, 0, x_80);
return x_1;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_box(0);
x_82 = lean_array_uset(x_50, x_66, x_81);
x_83 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_2, x_3, x_67);
x_84 = lean_array_uset(x_82, x_66, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_49);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_1, 0, x_85);
return x_1;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; lean_object* x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; size_t x_101; size_t x_102; lean_object* x_103; size_t x_104; size_t x_105; size_t x_106; lean_object* x_107; uint8_t x_108; 
x_86 = lean_ctor_get(x_1, 0);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_1);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_90 = x_86;
} else {
 lean_dec_ref(x_86);
 x_90 = lean_box(0);
}
x_91 = lean_array_get_size(x_89);
x_92 = l_Lean_Name_hash___override(x_2);
x_93 = lean_unsigned_to_nat(32u);
x_94 = lean_uint64_of_nat(x_93);
x_95 = lean_uint64_shift_right(x_92, x_94);
x_96 = lean_uint64_xor(x_92, x_95);
x_97 = lean_unsigned_to_nat(16u);
x_98 = lean_uint64_of_nat(x_97);
x_99 = lean_uint64_shift_right(x_96, x_98);
x_100 = lean_uint64_xor(x_96, x_99);
x_101 = lean_uint64_to_usize(x_100);
x_102 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_usize_of_nat(x_103);
x_105 = lean_usize_sub(x_102, x_104);
x_106 = lean_usize_land(x_101, x_105);
x_107 = lean_array_uget(x_89, x_106);
x_108 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_109 = lean_nat_add(x_88, x_103);
lean_dec(x_88);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_2);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 2, x_107);
x_111 = lean_array_uset(x_89, x_106, x_110);
x_112 = lean_unsigned_to_nat(2u);
x_113 = lean_nat_shiftl(x_109, x_112);
x_114 = lean_unsigned_to_nat(3u);
x_115 = lean_nat_div(x_113, x_114);
lean_dec(x_113);
x_116 = lean_array_get_size(x_111);
x_117 = lean_nat_dec_le(x_115, x_116);
lean_dec(x_116);
lean_dec(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_111);
if (lean_is_scalar(x_90)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_90;
}
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_87);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_4);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; 
if (lean_is_scalar(x_90)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_90;
}
lean_ctor_set(x_121, 0, x_109);
lean_ctor_set(x_121, 1, x_111);
x_122 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_87);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_4);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_box(0);
x_124 = lean_array_uset(x_89, x_106, x_123);
x_125 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_2, x_3, x_107);
x_126 = lean_array_uset(x_124, x_106, x_125);
if (lean_is_scalar(x_90)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_90;
}
lean_ctor_set(x_127, 0, x_88);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_87);
lean_ctor_set_uint8(x_128, sizeof(void*)*2, x_4);
return x_128;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_environment_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_ConstantInfo_name(x_2);
x_5 = l_Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0___redArg(x_3, x_4, x_2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*6, x_6);
return x_12;
}
}
LEAN_EXPORT uint8_t lean_kernel_diag_is_enabled(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_Diagnostics_isEnabled___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_kernel_diag_is_enabled(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_enableDiag(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_2);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_12 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*6, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_enableDiag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Kernel_Environment_enableDiag(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Kernel_Environment_isDiagnosticsEnabled(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_isDiagnosticsEnabled___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Kernel_Environment_isDiagnosticsEnabled(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_resetDiag(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
lean_ctor_set(x_13, 5, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*6, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_resetDiag___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Kernel_Environment_resetDiag(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_kernel_record_unfold(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_3 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
lean_inc(x_4);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_4, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(1u);
x_5 = x_10;
goto block_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
x_5 = x_13;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_4, x_2, x_5);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_3);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* lean_kernel_get_diag(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_kernel_set_diag(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*6, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
default: 
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_ConstantKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ConstantKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ConstantKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ConstantKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_ConstantKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_ConstantKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_instInhabitedConstantKind() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_ConstantKind_toCtorIdx(x_1);
x_4 = l_Lean_ConstantKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqConstantKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; lean_object* x_30; lean_object* x_39; lean_object* x_48; lean_object* x_57; lean_object* x_66; 
switch (x_1) {
case 0:
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_unsigned_to_nat(1024u);
x_76 = lean_nat_dec_le(x_75, x_2);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_unsigned_to_nat(2u);
x_78 = lean_nat_to_int(x_77);
x_3 = x_78;
goto block_11;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_to_int(x_79);
x_3 = x_80;
goto block_11;
}
}
case 1:
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_unsigned_to_nat(1024u);
x_82 = lean_nat_dec_le(x_81, x_2);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_unsigned_to_nat(2u);
x_84 = lean_nat_to_int(x_83);
x_12 = x_84;
goto block_20;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_to_int(x_85);
x_12 = x_86;
goto block_20;
}
}
case 2:
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_unsigned_to_nat(1024u);
x_88 = lean_nat_dec_le(x_87, x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_nat_to_int(x_89);
x_21 = x_90;
goto block_29;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_to_int(x_91);
x_21 = x_92;
goto block_29;
}
}
case 3:
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_unsigned_to_nat(1024u);
x_94 = lean_nat_dec_le(x_93, x_2);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_unsigned_to_nat(2u);
x_96 = lean_nat_to_int(x_95);
x_30 = x_96;
goto block_38;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_to_int(x_97);
x_30 = x_98;
goto block_38;
}
}
case 4:
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_unsigned_to_nat(1024u);
x_100 = lean_nat_dec_le(x_99, x_2);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_unsigned_to_nat(2u);
x_102 = lean_nat_to_int(x_101);
x_39 = x_102;
goto block_47;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_to_int(x_103);
x_39 = x_104;
goto block_47;
}
}
case 5:
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_unsigned_to_nat(1024u);
x_106 = lean_nat_dec_le(x_105, x_2);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_nat_to_int(x_107);
x_48 = x_108;
goto block_56;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_to_int(x_109);
x_48 = x_110;
goto block_56;
}
}
case 6:
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_unsigned_to_nat(1024u);
x_112 = lean_nat_dec_le(x_111, x_2);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_unsigned_to_nat(2u);
x_114 = lean_nat_to_int(x_113);
x_57 = x_114;
goto block_65;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_to_int(x_115);
x_57 = x_116;
goto block_65;
}
}
default: 
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_unsigned_to_nat(1024u);
x_118 = lean_nat_dec_le(x_117, x_2);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_unsigned_to_nat(2u);
x_120 = lean_nat_to_int(x_119);
x_66 = x_120;
goto block_74;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_to_int(x_121);
x_66 = x_122;
goto block_74;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.ConstantKind.defn", 22, 22);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.ConstantKind.thm", 21, 21);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.ConstantKind.axiom", 23, 23);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
block_38:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_31 = lean_mk_string_unchecked("Lean.ConstantKind.opaque", 24, 24);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = l_Repr_addAppParen(x_35, x_2);
return x_37;
}
block_47:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_mk_string_unchecked("Lean.ConstantKind.quot", 22, 22);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = l_Repr_addAppParen(x_44, x_2);
return x_46;
}
block_56:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_49 = lean_mk_string_unchecked("Lean.ConstantKind.induct", 24, 24);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = l_Repr_addAppParen(x_53, x_2);
return x_55;
}
block_65:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_58 = lean_mk_string_unchecked("Lean.ConstantKind.ctor", 22, 22);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = l_Repr_addAppParen(x_62, x_2);
return x_64;
}
block_74:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_67 = lean_mk_string_unchecked("Lean.ConstantKind.recursor", 26, 26);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_71, 0, x_69);
x_72 = lean_unbox(x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_72);
x_73 = l_Repr_addAppParen(x_71, x_2);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instReprConstantKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantKind_ofConstantInfo(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(2);
x_3 = lean_unbox(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
case 3:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(3);
x_9 = lean_unbox(x_8);
return x_9;
}
case 4:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(4);
x_11 = lean_unbox(x_10);
return x_11;
}
case 5:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(5);
x_13 = lean_unbox(x_12);
return x_13;
}
case 6:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(6);
x_15 = lean_unbox(x_14);
return x_15;
}
default: 
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(7);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantKind_ofConstantInfo___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_ConstantKind_ofConstantInfo(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedAsyncConstantInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
lean_inc(x_8);
x_9 = lean_task_pure(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_8);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_task_pure(x_13);
x_15 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_unbox(x_2);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_16);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_task_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_task_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncConstantInfo_ofConstantInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_ConstantInfo_name(x_1);
x_3 = l_Lean_ConstantKind_ofConstantInfo(x_1);
x_4 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_5 = lean_task_pure(x_4);
x_6 = lean_task_pure(x_1);
x_7 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_3);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_AsyncConstantInfo_isUnsafe(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = l_Lean_AsyncConstantInfo_toConstantInfo(x_1);
x_7 = l_Lean_ConstantInfo_isUnsafe(x_6);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AsyncConstantInfo_isUnsafe___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_AsyncConstantInfo_isUnsafe(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_AsyncContext_mayContain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_erase_macro_scopes(x_2);
x_5 = l_Lean_privateToUserName(x_4);
x_6 = l_Lean_Name_isPrefixOf(x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncContext_mayContain___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Environment_0__Lean_AsyncContext_mayContain(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedAsyncConsts() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_NameTrie_empty(lean_box(0));
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_instImpl____x40_Lean_Environment___hyg_1873_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = lean_box(0);
x_2 = lean_mk_string_unchecked("_private", 8, 8);
x_3 = l_Lean_Name_str___override(x_1, x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_str___override(x_3, x_4);
x_6 = lean_mk_string_unchecked("Environment", 11, 11);
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Name_num___override(x_7, x_8);
x_10 = l_Lean_Name_str___override(x_9, x_4);
x_11 = lean_mk_string_unchecked("AsyncConsts", 11, 11);
x_12 = l_Lean_Name_str___override(x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_instTypeNameAsyncConsts() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Environment_0__Lean_AsyncConsts_add_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_4);
x_5 = l_Lean_privateToUserName(x_4);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_inc(x_6);
x_7 = l_Lean_NameTrie_find_x3f___redArg(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_2);
x_14 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_13, x_4, x_2);
x_15 = l_Lean_NameTrie_insert(lean_box(0), x_6, x_5, x_2);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_19 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_20 = lean_mk_string_unchecked("_private.Lean.Environment.0.Lean.AsyncConsts.add", 48, 48);
x_21 = lean_unsigned_to_nat(432u);
x_22 = lean_unsigned_to_nat(4u);
x_23 = lean_mk_string_unchecked("duplicate normalized declaration name ", 38, 38);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
lean_inc(x_18);
x_26 = l_Lean_Name_toString(x_4, x_25, x_18);
x_27 = lean_string_append(x_23, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked(" vs. ", 5, 5);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_unbox(x_24);
x_33 = l_Lean_Name_toString(x_31, x_32, x_18);
x_34 = lean_string_append(x_29, x_33);
lean_dec(x_33);
x_35 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_19, x_20, x_21, x_22, x_34);
lean_dec(x_34);
lean_dec(x_20);
lean_dec(x_19);
x_36 = l_panic___at_____private_Lean_Environment_0__Lean_AsyncConsts_add_spec__0(x_1, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_NameMap_find_x3f(lean_box(0), x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___at_____private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_NamePart_cmp___boxed), 2, 0);
x_4 = lean_box(0);
x_5 = l_Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_findLongestPrefix_x3f___at_____private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTreeNode_findLongestPrefix_x3f___at_____private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_privateToUserName(x_2);
x_5 = l___private_Lean_Data_NameTrie_0__Lean_toKey(x_4);
lean_dec(x_4);
x_6 = l_Lean_PrefixTreeNode_findLongestPrefix_x3f___at_____private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f_spec__0___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findRec_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l___private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_name_eq(x_6, x_2);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_8 = l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_task_get_own(x_9);
x_11 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_10, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_1 = x_13;
goto _start;
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_task_pure(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask(x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l___private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_task_pure(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_dec(x_3);
x_9 = l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
x_10 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = lean_task_bind(x_11, x_10, x_12, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_2);
x_16 = lean_task_pure(x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Environment_0__Lean_Visibility_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ConstantKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_Visibility_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Environment_0__Lean_Visibility_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Visibility_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Environment_0__Lean_Visibility_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedVisibilityMap___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedVisibilityMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_get___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_get(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_get___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_VisibilityMap_get___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_VisibilityMap_get(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_VisibilityMap_map___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_const___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_VisibilityMap_const(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_asyncConsts(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_asyncConsts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Environment_0__Lean_Environment_asyncConsts(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_elab_environment_of_kernel_env(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc_n(x_1, 2);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_task_pure(x_1);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l_Lean_NameTrie_empty(lean_box(0));
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_task_pure(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
lean_ctor_set(x_15, 6, x_7);
lean_ctor_set(x_15, 7, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*8, x_16);
return x_15;
}
}
LEAN_EXPORT lean_object* lean_elab_environment_to_kernel_env(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_task_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setExporting(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_7);
lean_ctor_set(x_11, 5, x_8);
lean_ctor_set(x_11, 6, x_9);
lean_ctor_set(x_11, 7, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*8, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setExporting___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Environment_setExporting(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = lean_task_map(x_2, x_9, x_10, x_12);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 7);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_17);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*8, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_task_pure(x_2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_ctor_get(x_1, 6);
x_12 = lean_ctor_get(x_1, 7);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_14 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set(x_14, 4, x_9);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_11);
lean_ctor_set(x_14, 7, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_setCheckedSync___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isRealizing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 1);
x_7 = l_List_isEmpty___redArg(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isRealizing___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Environment_isRealizing(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_importEnv_x3f_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_importEnv_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_importEnv_x3f_unsafe__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_unlockAsync(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_box(0);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_ctor_get(x_1, 6);
x_9 = lean_ctor_get(x_1, 7);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_5);
lean_ctor_set(x_11, 4, x_6);
lean_ctor_set(x_11, 5, x_7);
lean_ctor_set(x_11, 6, x_8);
lean_ctor_set(x_11, 7, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_unlockAsync___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_unlockAsync(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_asyncMayContain(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_2);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l___private_Lean_Environment_0__Lean_AsyncContext_mayContain(x_6, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_asyncMayContain___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_asyncMayContain(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_addDeclCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_elab_add_decl(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_addDeclWithoutChecking___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_elab_add_decl_without_checking(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_addDeclCore___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Environment_0__Lean_AsyncContext_mayContain(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addDeclCore(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
goto block_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Environment_addDeclCore___lam__0___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_3);
x_13 = l_Lean_Declaration_getTopLevelNames(x_3);
x_14 = l_List_find_x3f(lean_box(0), x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_free_object(x_9);
lean_dec(x_11);
goto block_8;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_18 = lean_mk_string_unchecked("cannot add declaration ", 23, 23);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
lean_inc(x_17);
x_21 = l_Lean_Name_toString(x_16, x_20, x_17);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked(" to environment as it is restricted to the prefix ", 50, 50);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_unbox(x_19);
x_27 = l_Lean_Name_toString(x_25, x_26, x_17);
x_28 = lean_string_append(x_24, x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_14, 12);
lean_ctor_set(x_14, 0, x_28);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_31 = lean_mk_string_unchecked("cannot add declaration ", 23, 23);
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
lean_inc(x_30);
x_34 = l_Lean_Name_toString(x_29, x_33, x_30);
x_35 = lean_string_append(x_31, x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked(" to environment as it is restricted to the prefix ", 50, 50);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_unbox(x_32);
x_40 = l_Lean_Name_toString(x_38, x_39, x_30);
x_41 = lean_string_append(x_37, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_42);
return x_9;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_9, 0);
lean_inc(x_43);
lean_dec(x_9);
lean_inc(x_43);
x_44 = lean_alloc_closure((void*)(l_Lean_Environment_addDeclCore___lam__0___boxed), 2, 1);
lean_closure_set(x_44, 0, x_43);
lean_inc(x_3);
x_45 = l_Lean_Declaration_getTopLevelNames(x_3);
x_46 = l_List_find_x3f(lean_box(0), x_44, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_dec(x_43);
goto block_8;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
lean_dec(x_1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_50 = lean_mk_string_unchecked("cannot add declaration ", 23, 23);
x_51 = lean_box(1);
x_52 = lean_unbox(x_51);
lean_inc(x_49);
x_53 = l_Lean_Name_toString(x_47, x_52, x_49);
x_54 = lean_string_append(x_50, x_53);
lean_dec(x_53);
x_55 = lean_mk_string_unchecked(" to environment as it is restricted to the prefix ", 50, 50);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_ctor_get(x_43, 0);
lean_inc(x_57);
lean_dec(x_43);
x_58 = lean_unbox(x_51);
x_59 = l_Lean_Name_toString(x_57, x_58, x_49);
x_60 = lean_string_append(x_56, x_59);
lean_dec(x_59);
if (lean_is_scalar(x_48)) {
 x_61 = lean_alloc_ctor(12, 1, 0);
} else {
 x_61 = x_48;
 lean_ctor_set_tag(x_61, 12);
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
block_8:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_elab_add_decl_without_checking(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_elab_add_decl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addDeclCore___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_addDeclCore___lam__0(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addDeclCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Environment_addDeclCore(x_1, x_6, x_3, x_4, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_constants(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_elab_environment_to_kernel_env(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_const2ModIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_elab_environment_to_kernel_env(x_1);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_lakeAdd___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = l_Lean_AsyncConstantInfo_ofConstantInfo(x_1);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = l_Lean_NameTrie_empty(lean_box(0));
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_task_pure(x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_12);
x_14 = l___private_Lean_Environment_0__Lean_AsyncConsts_add(x_3, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* lake_environment_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_3 = l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_Environment_lakeAdd___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_task_get_own(x_5);
x_7 = lean_environment_add(x_6, x_2);
x_8 = l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(x_1, x_7);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 3);
lean_inc(x_12);
x_13 = l___private_Lean_Environment_0__Lean_VisibilityMap_map___redArg(x_12, x_4);
x_14 = lean_ctor_get(x_8, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 7);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set(x_19, 6, x_16);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*8, x_18);
return x_19;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_name_eq(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_5;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(5u);
x_6 = lean_usize_of_nat(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_shift_left(x_8, x_6);
x_10 = lean_usize_sub(x_9, x_8);
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_14 = lean_array_get(x_13, x_4, x_12);
lean_dec(x_12);
lean_dec(x_4);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_name_eq(x_3, x_15);
lean_dec(x_15);
return x_16;
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_usize_shift_right(x_2, x_6);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___redArg(x_22, x_23, x_3);
lean_dec(x_22);
return x_24;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
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
x_23 = lean_array_uget(x_6, x_22);
lean_dec(x_6);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___redArg(x_5, x_2);
return x_25;
}
else
{
lean_dec(x_5);
return x_24;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; uint8_t x_45; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = l_Lean_Name_hash___override(x_2);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_27, x_43);
lean_dec(x_27);
x_45 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_44);
lean_dec(x_44);
return x_45;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addExtraName___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
x_9 = l_Lean_NameSet_insert(x_8, x_1);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set(x_11, 5, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*6, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addExtraName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_3 = l_Lean_Environment_constants(x_1);
x_4 = l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Environment_addExtraName___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_1, x_5);
return x_6;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_isReservedName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_reserved_name(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findAsyncCore_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Environment_0__Lean_Environment_asyncConsts(x_1);
x_5 = l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l___private_Lean_Environment_0__Lean_AsyncConsts_findRec_x3f(x_4, x_2);
if (lean_obj_tag(x_6) == 0)
{
if (x_3 == 0)
{
uint8_t x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_is_reserved_name(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 7);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_task_get_own(x_9);
x_11 = l_Lean_NameMap_find_x3f(lean_box(0), x_10, x_2);
lean_dec(x_2);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findAsyncCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l___private_Lean_Environment_0__Lean_Environment_findAsyncCore_x3f(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_NameMap_find_x3f(lean_box(0), x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_9; 
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_14; 
lean_inc(x_1);
x_14 = lean_is_reserved_name(x_1, x_3);
if (x_14 == 0)
{
x_9 = x_14;
goto block_13;
}
else
{
if (x_4 == 0)
{
x_9 = x_14;
goto block_13;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
goto block_8;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_5, 0, x_17);
x_18 = lean_task_pure(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_task_pure(x_21);
return x_22;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_task_pure(x_6);
return x_7;
}
block_13:
{
if (x_9 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
goto block_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 7);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_task_map(x_2, x_10, x_11, x_9);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Environment_0__Lean_Environment_asyncConsts(x_1);
x_5 = l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_box(x_3);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_7);
x_9 = l___private_Lean_Environment_0__Lean_AsyncConsts_findRecTask(x_4, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = lean_task_bind(x_9, x_8, x_10, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_5, 0, x_16);
x_17 = lean_task_pure(x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_task_pure(x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l___private_Lean_Environment_0__Lean_Environment_findTaskCore___lam__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_findTaskCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l___private_Lean_Environment_0__Lean_Environment_findTaskCore(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_findAsync_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_4 = x_36;
goto block_33;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_4 = x_38;
goto block_33;
}
block_33:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_2);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_7, x_23);
lean_dec(x_7);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_2, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = l___private_Lean_Environment_0__Lean_Environment_findAsyncCore_x3f(x_1, x_2, x_3);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = l_Lean_AsyncConstantInfo_ofConstantInfo(x_28);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l_Lean_AsyncConstantInfo_ofConstantInfo(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_findAsync_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_findTask(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_4 = x_38;
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_4 = x_40;
goto block_35;
}
block_35:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_2);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_7, x_23);
lean_dec(x_7);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_2, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = l___private_Lean_Environment_0__Lean_Environment_findTaskCore(x_1, x_2, x_3);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = l_Lean_AsyncConstantInfo_ofConstantInfo(x_28);
lean_ctor_set(x_25, 0, x_29);
x_30 = lean_task_pure(x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
lean_dec(x_25);
x_32 = l_Lean_AsyncConstantInfo_ofConstantInfo(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_task_pure(x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_findTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Environment_findTask(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_findConstVal_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_41; 
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_4 = x_43;
goto block_40;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_4 = x_45;
goto block_40;
}
block_40:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_2);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_7, x_23);
lean_dec(x_7);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_2, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = l___private_Lean_Environment_0__Lean_Environment_findAsyncCore_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_Lean_AsyncConstantInfo_toConstantVal(x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l_Lean_AsyncConstantInfo_toConstantVal(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = l_Lean_ConstantInfo_toConstantVal(x_35);
lean_dec(x_35);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
lean_dec(x_25);
x_38 = l_Lean_ConstantInfo_toConstantVal(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_findConstVal_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Environment_findConstVal_x3f(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_find_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_4 = x_36;
goto block_33;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_4 = x_38;
goto block_33;
}
block_33:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_2);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_7, x_23);
lean_dec(x_7);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_2, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = l___private_Lean_Environment_0__Lean_Environment_findAsyncCore_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_26) == 0)
{
return x_25;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_AsyncConstantInfo_toConstantInfo(x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_AsyncConstantInfo_toConstantInfo(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Environment_find_x3f(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_enableRealizationsForConst_unsafe__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_enableRealizationsForConst_unsafe__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_enableRealizationsForConst_unsafe__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_instMonadEIO(lean_box(0));
x_4 = lean_box(0);
x_5 = l_instInhabitedOfMonad___redArg(x_3, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_enableRealizationsForConst___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_enableRealizationsForConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_box(0);
x_40 = lean_unbox(x_39);
lean_inc(x_3);
lean_inc(x_1);
x_41 = l_Lean_Environment_findAsync_x3f(x_1, x_3, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_2);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_43 = lean_box(1);
x_44 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_45 = lean_mk_string_unchecked("Lean.Environment.enableRealizationsForConst", 43, 43);
x_46 = lean_unsigned_to_nat(800u);
x_47 = lean_unsigned_to_nat(4u);
x_48 = lean_mk_string_unchecked("declaration ", 12, 12);
x_49 = lean_unbox(x_43);
x_50 = l_Lean_Name_toString(x_3, x_49, x_42);
x_51 = lean_string_append(x_48, x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked(" not found in environment", 25, 25);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_44, x_45, x_46, x_47, x_53);
lean_dec(x_53);
lean_dec(x_45);
lean_dec(x_44);
x_55 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_54, x_4);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; 
lean_dec(x_41);
x_60 = lean_ctor_get(x_1, 4);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
x_5 = x_4;
goto block_38;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_3);
x_62 = l___private_Lean_Environment_0__Lean_AsyncContext_mayContain(x_61, x_3);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_2);
x_63 = lean_box(x_62);
x_64 = lean_alloc_closure((void*)(l_Lean_Environment_enableRealizationsForConst___lam__1___boxed), 2, 1);
lean_closure_set(x_64, 0, x_63);
x_65 = lean_box(1);
x_66 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_67 = lean_mk_string_unchecked("Lean.Environment.enableRealizationsForConst", 43, 43);
x_68 = lean_unsigned_to_nat(804u);
x_69 = lean_unsigned_to_nat(6u);
x_70 = lean_unbox(x_65);
lean_inc(x_64);
x_71 = l_Lean_Name_toString(x_3, x_70, x_64);
x_72 = lean_mk_string_unchecked(" is outside current context ", 28, 28);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_61, 0);
lean_inc(x_74);
lean_dec(x_61);
x_75 = lean_unbox(x_65);
x_76 = l_Lean_Name_toString(x_74, x_75, x_64);
x_77 = lean_string_append(x_73, x_76);
lean_dec(x_76);
x_78 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_66, x_67, x_68, x_69, x_77);
lean_dec(x_77);
lean_dec(x_67);
lean_dec(x_66);
x_79 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_78, x_4);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_1);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_dec(x_61);
x_5 = x_4;
goto block_38;
}
}
}
block_38:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 6);
lean_inc(x_6);
x_7 = l_Lean_NameMap_contains(lean_box(0), x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_box(0);
x_9 = lean_st_mk_ref(x_8, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_11);
x_19 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_6, x_3, x_18);
x_20 = lean_ctor_get(x_1, 7);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_15);
lean_ctor_set(x_22, 4, x_16);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set(x_22, 7, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*8, x_21);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 5);
lean_inc(x_30);
lean_inc(x_1);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_23);
x_32 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_6, x_3, x_31);
x_33 = lean_ctor_get(x_1, 7);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
lean_ctor_set(x_35, 5, x_30);
lean_ctor_set(x_35, 6, x_32);
lean_ctor_set(x_35, 7, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*8, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_enableRealizationsForConst___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Environment_enableRealizationsForConst___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed), 1, 0);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_9, x_11, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_12);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed), 1, 0);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Name_toString(x_18, x_20, x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_15;
x_2 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_mk_string_unchecked(", ", 2, 2);
x_6 = lean_string_append(x_1, x_5);
lean_dec(x_5);
x_7 = lean_string_append(x_6, x_3);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_string_append(x_5, x_4);
x_7 = lean_mk_string_unchecked("]", 1, 1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_mk_string_unchecked("[", 1, 1);
x_11 = lean_string_append(x_10, x_9);
x_12 = l_List_foldl___at___List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2_spec__2(x_11, x_3);
x_13 = lean_unsigned_to_nat(93u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_string_push(x_12, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_dbgFormatAsyncState_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___redArg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_11, x_3);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_13);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__0(x_15, x_16);
lean_ctor_set(x_7, 1, x_17);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_14;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_22, x_3);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_24);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__0(x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_29);
{
lean_object* _tmp_0 = x_19;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_25;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_36, x_3);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_38);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__0(x_40, x_41);
if (lean_is_scalar(x_35)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_35;
}
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
x_1 = x_32;
x_2 = x_44;
x_3 = x_39;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_dbgFormatAsyncState_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___redArg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_11, x_3);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_13);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__0(x_15, x_16);
lean_ctor_set(x_7, 1, x_17);
lean_ctor_set(x_1, 1, x_2);
x_18 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_dbgFormatAsyncState_spec__4_spec__4(x_9, x_1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_22, x_3);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_24);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__0(x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_29);
x_30 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_dbgFormatAsyncState_spec__4_spec__4(x_19, x_1, x_25);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_36, x_3);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_38);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__0(x_40, x_41);
if (lean_is_scalar(x_35)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_35;
}
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
x_45 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_dbgFormatAsyncState_spec__4_spec__4(x_32, x_44, x_39);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("none", 4, 4);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_mk_string_unchecked("some ", 5, 5);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_7);
x_8 = lean_unsigned_to_nat(1024u);
x_9 = l_Lean_Name_reprPrec(x_6, x_8);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Repr_addAppParen(x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("some ", 5, 5);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_unsigned_to_nat(1024u);
x_16 = l_Lean_Name_reprPrec(x_12, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_alloc_closure((void*)(l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg___lam__0), 1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = l_Std_Format_joinSep(lean_box(0), x_4, x_1, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_mk_string_unchecked("(", 1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Name_reprPrec(x_3, x_6);
x_8 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_9 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg(x_4);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = l_List_reverse___redArg(x_10);
x_12 = lean_mk_string_unchecked(",", 1, 1);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_11, x_15);
x_17 = lean_mk_string_unchecked(")", 1, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_to_int(x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = lean_mk_string_unchecked("(", 1, 1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Name_reprPrec(x_28, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_reverse___redArg(x_36);
x_38 = lean_mk_string_unchecked(",", 1, 1);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(1);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_37, x_41);
x_43 = lean_mk_string_unchecked(")", 1, 1);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_30);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_alloc_closure((void*)(l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___redArg___lam__0), 1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = l_Std_Format_joinSep(lean_box(0), x_4, x_1, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_mk_string_unchecked("(", 1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Name_reprPrec(x_3, x_6);
x_8 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_9 = l_String_quote(x_4);
lean_dec(x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_List_reverse___redArg(x_11);
x_13 = lean_mk_string_unchecked(",", 1, 1);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_12, x_16);
x_18 = lean_mk_string_unchecked(")", 1, 1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_to_int(x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_5);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = lean_mk_string_unchecked("(", 1, 1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Name_reprPrec(x_29, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_String_quote(x_30);
lean_dec(x_30);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_List_reverse___redArg(x_38);
x_40 = lean_mk_string_unchecked(",", 1, 1);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_39, x_43);
x_45 = lean_mk_string_unchecked(")", 1, 1);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_to_int(x_46);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_31);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_alloc_closure((void*)(l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___redArg___lam__0), 1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = l_Std_Format_joinSep(lean_box(0), x_4, x_1, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("none", 4, 4);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_mk_string_unchecked("some ", 5, 5);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_7);
x_8 = l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___redArg(x_6);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("some ", 5, 5);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___redArg(x_11);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg___lam__0), 3, 0);
x_3 = l_Lean_Name_instBEq;
x_4 = l_Lean_instHashableName;
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_3, x_4, lean_box(0), lean_box(0), x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__16(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_task_get_own(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1(x_11, x_12);
x_14 = l_List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2(x_13);
lean_dec(x_13);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_task_get_own(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1(x_21, x_22);
x_24 = l_List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_25);
{
lean_object* _tmp_0 = x_16;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = lean_task_get_own(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1(x_34, x_35);
x_37 = l_List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2(x_36);
lean_dec(x_36);
if (lean_is_scalar(x_31)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_31;
}
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_2);
x_1 = x_28;
x_2 = x_39;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_dbgFormatAsyncState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_52; lean_object* x_53; lean_object* x_64; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc(x_3);
x_4 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_3);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_List_mapM_loop___at___Lean_Environment_dbgFormatAsyncState_spec__4(x_4, x_5, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_64 = lean_ctor_get(x_1, 5);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_52 = x_65;
x_53 = x_8;
goto block_63;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_67, 2);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_get(x_68, x_8);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_70);
lean_dec(x_70);
x_73 = lean_box(0);
x_74 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__16(x_72, x_73);
lean_ctor_set(x_64, 0, x_74);
x_52 = x_64;
x_53 = x_71;
goto block_63;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec(x_64);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_get(x_76, x_8);
lean_dec(x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_78);
lean_dec(x_78);
x_81 = lean_box(0);
x_82 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__16(x_80, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_52 = x_83;
x_53 = x_79;
goto block_63;
}
}
block_51:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(x_13, x_14);
x_16 = lean_unsigned_to_nat(120u);
x_17 = lean_format_pretty(x_15, x_16, x_14, x_14);
x_18 = lean_string_append(x_12, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("\nasyncConsts: ", 14, 14);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = l___private_Lean_Environment_0__Lean_Environment_asyncConsts(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_List_reverse___redArg(x_22);
x_24 = lean_box(0);
x_25 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__7(x_23, x_24);
x_26 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg(x_25);
x_27 = lean_format_pretty(x_26, x_16, x_14, x_14);
x_28 = lean_string_append(x_20, x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("\nrealizedLocalConsts: ", 22, 22);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___redArg(x_7);
x_32 = lean_format_pretty(x_31, x_16, x_14, x_14);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = lean_mk_string_unchecked("\n  \nrealizedImportedConsts\?: ", 29, 29);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11(x_10, x_14);
x_37 = lean_format_pretty(x_36, x_16, x_14, x_14);
x_38 = lean_string_append(x_35, x_37);
lean_dec(x_37);
x_39 = lean_mk_string_unchecked("\n  \nbase.private.constants.map₂: ", 35, 33);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(x_44);
lean_dec(x_44);
x_46 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__15(x_45, x_24);
x_47 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg(x_46);
x_48 = lean_format_pretty(x_47, x_16, x_14, x_14);
x_49 = lean_string_append(x_40, x_48);
lean_dec(x_48);
if (lean_is_scalar(x_9)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_9;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_11);
return x_50;
}
block_63:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_mk_string_unchecked("asyncCtx.declPrefix: ", 21, 21);
x_55 = lean_ctor_get(x_1, 4);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_10 = x_52;
x_11 = x_53;
x_12 = x_54;
x_13 = x_56;
goto block_51;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
lean_ctor_set(x_55, 0, x_59);
x_10 = x_52;
x_11 = x_53;
x_12 = x_54;
x_13 = x_55;
goto block_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_10 = x_52;
x_11 = x_53;
x_12 = x_54;
x_13 = x_62;
goto block_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___Lean_Environment_dbgFormatAsyncState_spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9_spec__9(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__9(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11_spec__11(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11_spec__11(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__11(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_dbgFormatCheckedSyncState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_mk_string_unchecked("checked.get.constants.map₂: ", 30, 28);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_task_get_own(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_PersistentHashMap_toList___at___Lean_Environment_dbgFormatAsyncState_spec__14___redArg(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__15(x_8, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_repr___at___Lean_Environment_dbgFormatAsyncState_spec__8___redArg(x_10);
x_13 = lean_unsigned_to_nat(120u);
x_14 = lean_format_pretty(x_12, x_13, x_11, x_11);
x_15 = lean_string_append(x_3, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizingStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizingStack___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_realizingStack(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_enterAsync(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_erase_macro_scopes(x_1);
x_8 = l_Lean_privateToUserName(x_7);
x_9 = l_Lean_Environment_realizingStack(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_6);
lean_ctor_set(x_16, 4, x_11);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_16, 6, x_13);
lean_ctor_set(x_16, 7, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*8, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_enterAsync___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_Environment_enterAsync(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_enterAsyncRealizing(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_box(0);
x_8 = l_Lean_Environment_realizingStack(x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_6);
lean_ctor_set(x_16, 4, x_11);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_16, 6, x_13);
lean_ctor_set(x_16, 7, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*8, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_enterAsyncRealizing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_Environment_enterAsyncRealizing(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_promiseChecked___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_task_pure(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_promiseChecked(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_io_promise_new(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Environment_promiseChecked___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_io_promise_result_opt(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = lean_task_bind(x_9, x_6, x_10, x_12);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 7);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_20 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_17);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*8, x_19);
x_21 = lean_mk_string_unchecked("__reserved__Environment_promiseChecked", 38, 38);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l___private_Lean_Environment_0__Lean_Environment_enterAsync(x_22, x_1);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_3, 0, x_24);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Environment_promiseChecked___lam__0___boxed), 2, 1);
lean_closure_set(x_27, 0, x_1);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_io_promise_result_opt(x_25);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
x_34 = lean_task_bind(x_30, x_27, x_31, x_33);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 7);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_41 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_35);
lean_ctor_set(x_41, 4, x_36);
lean_ctor_set(x_41, 5, x_37);
lean_ctor_set(x_41, 6, x_38);
lean_ctor_set(x_41, 7, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*8, x_40);
x_42 = lean_mk_string_unchecked("__reserved__Environment_promiseChecked", 38, 38);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = l___private_Lean_Environment_0__Lean_Environment_enterAsync(x_43, x_1);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_25);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_26);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_promiseChecked___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_promiseChecked___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_5 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_6 = lean_mk_string_unchecked("Lean.Environment.PromiseCheckedResult.commitChecked", 51, 51);
x_7 = lean_unsigned_to_nat(882u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_mk_string_unchecked("assertion violation: env.asyncCtx\?.isSome\n  ", 44, 44);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_10, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_12 = lean_elab_environment_to_kernel_env(x_2);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_io_promise_resolve(x_12, x_13, x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_PromiseCheckedResult_commitChecked(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedConstantInfo;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("sorryAx", 7, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Level_ofNat(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_5);
x_10 = l_Lean_Expr_const___override(x_5, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Level_ofNat(x_11);
lean_inc(x_12);
x_13 = l_Lean_Expr_sort___override(x_12);
x_14 = lean_mk_string_unchecked("Bool", 4, 4);
x_15 = lean_mk_string_unchecked("true", 4, 4);
x_16 = l_Lean_Name_mkStr2(x_14, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_8);
lean_inc(x_17);
x_18 = l_Lean_mkAppB(x_10, x_13, x_17);
lean_inc(x_18);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_box(x_2);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_8);
x_22 = l_Lean_Expr_const___override(x_5, x_21);
x_23 = l_Lean_mkAppB(x_22, x_18, x_17);
x_24 = lean_box(1);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_3);
x_27 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_unbox(x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_8);
x_31 = l_Lean_Expr_const___override(x_5, x_30);
x_32 = l_Lean_mkAppB(x_31, x_18, x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_3);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
case 2:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_19);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_40 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_41 = lean_mk_string_unchecked("_private.Lean.Environment.0.Lean.Environment.mkFallbackConstInfo", 64, 64);
x_42 = lean_unsigned_to_nat(937u);
x_43 = lean_unsigned_to_nat(11u);
x_44 = lean_mk_string_unchecked("unsupported constant kind ", 26, 26);
x_45 = l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248_(x_2, x_11);
x_46 = lean_unsigned_to_nat(120u);
x_47 = lean_format_pretty(x_45, x_46, x_11, x_11);
x_48 = lean_string_append(x_44, x_47);
lean_dec(x_47);
x_49 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_40, x_41, x_42, x_43, x_48);
lean_dec(x_48);
lean_dec(x_41);
lean_dec(x_40);
x_50 = l_panic___at_____private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo_spec__0(x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 7);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_task_pure(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__3(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__4(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo(x_1, x_2);
x_5 = l_Lean_ConstantInfo_toConstantVal(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = l_Lean_NameTrie_empty(lean_box(0));
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_9, 3);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = l_Lean_NameTrie_empty(lean_box(0));
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_9, 3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_58; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Environment_addConstAsync___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Environment_addConstAsync___lam__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Environment_promiseChecked___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_box(x_4);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Environment_addConstAsync___lam__3___boxed), 3, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_box(x_3);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Environment_addConstAsync___lam__2___boxed), 3, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_box(x_3);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Environment_addConstAsync___lam__4___boxed), 3, 2);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
x_18 = lean_alloc_closure((void*)(l_Lean_Environment_addConstAsync___lam__5___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Environment_addConstAsync___lam__6___boxed), 2, 1);
lean_closure_set(x_19, 0, x_17);
if (x_6 == 0)
{
x_58 = x_7;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_1, 4);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
x_58 = x_7;
goto block_86;
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_2);
x_90 = l___private_Lean_Environment_0__Lean_AsyncContext_mayContain(x_89, x_2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_91 = lean_box(x_90);
x_92 = lean_alloc_closure((void*)(l_Lean_Environment_enableRealizationsForConst___lam__1___boxed), 2, 1);
lean_closure_set(x_92, 0, x_91);
x_93 = lean_mk_string_unchecked("cannot add declaration ", 23, 23);
lean_inc(x_92);
x_94 = l_Lean_Name_toString(x_2, x_6, x_92);
x_95 = lean_string_append(x_93, x_94);
lean_dec(x_94);
x_96 = lean_mk_string_unchecked(" to environment as it is restricted to the prefix ", 50, 50);
x_97 = lean_string_append(x_95, x_96);
lean_dec(x_96);
x_98 = lean_ctor_get(x_89, 0);
lean_inc(x_98);
lean_dec(x_89);
x_99 = l_Lean_Name_toString(x_98, x_6, x_92);
x_100 = lean_string_append(x_97, x_99);
lean_dec(x_99);
lean_ctor_set_tag(x_87, 18);
lean_ctor_set(x_87, 0, x_100);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_87);
lean_ctor_set(x_101, 1, x_7);
return x_101;
}
else
{
lean_free_object(x_87);
lean_dec(x_89);
x_58 = x_7;
goto block_86;
}
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_87, 0);
lean_inc(x_102);
lean_dec(x_87);
lean_inc(x_2);
x_103 = l___private_Lean_Environment_0__Lean_AsyncContext_mayContain(x_102, x_2);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_104 = lean_box(x_103);
x_105 = lean_alloc_closure((void*)(l_Lean_Environment_enableRealizationsForConst___lam__1___boxed), 2, 1);
lean_closure_set(x_105, 0, x_104);
x_106 = lean_mk_string_unchecked("cannot add declaration ", 23, 23);
lean_inc(x_105);
x_107 = l_Lean_Name_toString(x_2, x_6, x_105);
x_108 = lean_string_append(x_106, x_107);
lean_dec(x_107);
x_109 = lean_mk_string_unchecked(" to environment as it is restricted to the prefix ", 50, 50);
x_110 = lean_string_append(x_108, x_109);
lean_dec(x_109);
x_111 = lean_ctor_get(x_102, 0);
lean_inc(x_111);
lean_dec(x_102);
x_112 = l_Lean_Name_toString(x_111, x_6, x_105);
x_113 = lean_string_append(x_110, x_112);
lean_dec(x_112);
x_114 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_7);
return x_115;
}
else
{
lean_dec(x_102);
x_58 = x_7;
goto block_86;
}
}
}
}
block_57:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_28);
lean_inc(x_25);
x_31 = lean_task_map(x_19, x_25, x_28, x_21);
lean_inc(x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_28);
lean_inc(x_25);
x_33 = lean_task_map(x_12, x_25, x_28, x_21);
lean_inc(x_2);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_4);
lean_inc(x_28);
x_35 = lean_task_map(x_18, x_25, x_28, x_21);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_io_promise_result_opt(x_26);
lean_inc(x_28);
x_40 = lean_task_bind(x_39, x_10, x_28, x_21);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = l___private_Lean_Environment_0__Lean_AsyncConsts_add(x_42, x_32);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_Environment_0__Lean_AsyncConsts_add(x_44, x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_ctor_get(x_1, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 6);
lean_inc(x_49);
x_50 = lean_io_promise_result_opt(x_24);
x_51 = lean_task_bind(x_50, x_9, x_28, x_21);
x_52 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_53 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_40);
lean_ctor_set(x_53, 3, x_46);
lean_ctor_set(x_53, 4, x_47);
lean_ctor_set(x_53, 5, x_48);
lean_ctor_set(x_53, 6, x_49);
lean_ctor_set(x_53, 7, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*8, x_52);
lean_inc(x_2);
x_54 = l___private_Lean_Environment_0__Lean_Environment_enterAsync(x_2, x_1);
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_2);
lean_ctor_set(x_55, 3, x_29);
lean_ctor_set(x_55, 4, x_23);
lean_ctor_set(x_55, 5, x_26);
lean_ctor_set(x_55, 6, x_24);
lean_ctor_set_uint8(x_55, sizeof(void*)*7, x_3);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_20);
return x_56;
}
block_86:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_59 = lean_io_promise_new(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_io_promise_new(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_io_promise_new(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_io_promise_new(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_io_promise_result_opt(x_60);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
x_75 = lean_task_map(x_16, x_71, x_72, x_74);
x_76 = lean_io_promise_result_opt(x_63);
x_77 = lean_unbox(x_73);
lean_inc(x_76);
x_78 = lean_task_map(x_14, x_76, x_72, x_77);
lean_inc(x_75);
lean_inc(x_2);
x_79 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_79, 0, x_2);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*3, x_3);
if (x_5 == 0)
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_8);
x_80 = lean_box(0);
x_81 = lean_unbox(x_73);
x_20 = x_70;
x_21 = x_81;
x_22 = x_79;
x_23 = x_63;
x_24 = x_66;
x_25 = x_76;
x_26 = x_69;
x_27 = x_75;
x_28 = x_72;
x_29 = x_60;
x_30 = x_80;
goto block_57;
}
else
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_unbox(x_73);
lean_inc(x_76);
x_83 = lean_task_map(x_8, x_76, x_72, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_unbox(x_73);
x_20 = x_70;
x_21 = x_85;
x_22 = x_79;
x_23 = x_63;
x_24 = x_66;
x_25 = x_76;
x_26 = x_69;
x_27 = x_75;
x_28 = x_72;
x_29 = x_60;
x_30 = x_84;
goto block_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_addConstAsync___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_addConstAsync___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Environment_addConstAsync___lam__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Environment_addConstAsync___lam__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Environment_addConstAsync___lam__4(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_addConstAsync___lam__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___lam__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_addConstAsync___lam__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addConstAsync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_Lean_Environment_addConstAsync(x_1, x_2, x_8, x_9, x_10, x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_AddConstAsyncResult_commitSignature(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_name_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Environment_enableRealizationsForConst___lam__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_box(1);
x_10 = lean_mk_string_unchecked("AddConstAsyncResult.commitSignature: constant has name ", 55, 55);
x_11 = lean_unbox(x_9);
lean_inc(x_8);
x_12 = l_Lean_Name_toString(x_4, x_11, x_8);
x_13 = lean_string_append(x_10, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked(" but expected ", 14, 14);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_unbox(x_9);
x_17 = l_Lean_Name_toString(x_5, x_16, x_8);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_io_promise_resolve(x_2, x_21, x_3);
lean_dec(x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed), 1, 0);
x_6 = lean_mk_string_unchecked(", ", 2, 2);
x_7 = lean_string_append(x_1, x_6);
lean_dec(x_6);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Name_toString(x_3, x_9, x_5);
x_11 = lean_string_append(x_7, x_10);
lean_dec(x_10);
x_1 = x_11;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_6 = lean_mk_string_unchecked("[", 1, 1);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Name_toString(x_4, x_8, x_5);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("]", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_15 = lean_mk_string_unchecked("[", 1, 1);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Name_toString(x_13, x_17, x_14);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = l_List_foldl___at___List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0_spec__0(x_19, x_3);
x_21 = lean_unsigned_to_nat(93u);
x_22 = l_Char_ofNat(x_21);
x_23 = lean_string_push(x_20, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_31; lean_object* x_32; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_144 = lean_box(0);
x_145 = lean_unbox(x_144);
x_146 = l_Lean_Environment_setExporting(x_2, x_145);
x_147 = lean_ctor_get(x_1, 2);
lean_inc(x_147);
x_148 = lean_unbox(x_144);
lean_inc(x_147);
x_149 = l_Lean_Environment_find_x3f(x_146, x_147, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_4);
lean_dec(x_1);
x_150 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_151 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: constant ", 42, 42);
x_152 = lean_box(1);
x_153 = lean_unbox(x_152);
x_154 = l_Lean_Name_toString(x_147, x_153, x_150);
x_155 = lean_string_append(x_151, x_154);
lean_dec(x_154);
x_156 = lean_mk_string_unchecked(" not found in async context", 27, 27);
x_157 = lean_string_append(x_155, x_156);
lean_dec(x_156);
x_158 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_5);
return x_159;
}
else
{
lean_object* x_160; 
lean_dec(x_147);
x_160 = lean_ctor_get(x_149, 0);
lean_inc(x_160);
lean_dec(x_149);
x_31 = x_160;
x_32 = x_5;
goto block_143;
}
}
else
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_3, 0);
lean_inc(x_161);
lean_dec(x_3);
x_31 = x_161;
x_32 = x_5;
goto block_143;
}
block_20:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_10, 3);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_io_promise_resolve(x_13, x_14, x_6);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
block_30:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_Environment_setExporting(x_2, x_21);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
x_27 = l_Lean_Environment_find_x3f(x_25, x_26, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_inc(x_22);
x_6 = x_24;
x_7 = x_22;
x_8 = x_22;
goto block_20;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_6 = x_24;
x_7 = x_22;
x_8 = x_28;
goto block_20;
}
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_6 = x_24;
x_7 = x_22;
x_8 = x_29;
goto block_20;
}
}
block_143:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_ConstantInfo_toConstantVal(x_31);
lean_inc(x_33);
lean_inc(x_1);
x_34 = l_Lean_Environment_AddConstAsyncResult_commitSignature(x_1, x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = l_Lean_ConstantKind_ofConstantInfo(x_31);
x_39 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_40 = l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230_(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_1);
x_41 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: constant has kind ", 51, 51);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248_(x_38, x_42);
x_44 = lean_unsigned_to_nat(120u);
x_45 = lean_format_pretty(x_43, x_44, x_42, x_42);
x_46 = lean_string_append(x_41, x_45);
lean_dec(x_45);
x_47 = lean_mk_string_unchecked(" but expected ", 14, 14);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248_(x_39, x_42);
x_50 = lean_format_pretty(x_49, x_44, x_42, x_42);
x_51 = lean_string_append(x_48, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_52);
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
x_54 = l_IO_Promise_result_x21___redArg(x_53);
lean_dec(x_53);
x_55 = lean_task_get_own(x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = l_Lean_ConstantInfo_levelParams(x_31);
x_58 = l_List_beq___at_____private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431__spec__0(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_1);
x_59 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: constant has level params ", 59, 59);
x_60 = l_List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0(x_57);
x_61 = lean_string_append(x_59, x_60);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked(" but expected ", 14, 14);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = l_List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0(x_56);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_66);
return x_34;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_57);
lean_dec(x_56);
x_67 = lean_ctor_get(x_55, 2);
lean_inc(x_67);
lean_dec(x_55);
x_68 = l_Lean_ConstantInfo_type(x_31);
x_69 = lean_expr_eqv(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_1);
x_70 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: constant has type ", 51, 51);
x_71 = lean_expr_dbg_to_string(x_68);
lean_dec(x_68);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked(" but expected ", 14, 14);
x_74 = lean_string_append(x_72, x_73);
lean_dec(x_73);
x_75 = lean_expr_dbg_to_string(x_67);
lean_dec(x_67);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_77);
return x_34;
}
else
{
lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_67);
x_78 = lean_box(0);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_79; 
lean_free_object(x_34);
lean_dec(x_33);
x_79 = lean_unbox(x_78);
x_21 = x_69;
x_22 = x_31;
x_23 = x_79;
x_24 = x_36;
goto block_30;
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_4, 0);
lean_inc(x_80);
x_81 = l_Lean_ConstantInfo_toConstantVal(x_80);
lean_dec(x_80);
x_82 = l___private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431_(x_81, x_33);
lean_dec(x_33);
lean_dec(x_81);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_31);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_4);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_4, 0);
lean_dec(x_84);
x_85 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: exported constant has different signature", 74, 74);
lean_ctor_set_tag(x_4, 18);
lean_ctor_set(x_4, 0, x_85);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_4);
return x_34;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_4);
x_86 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: exported constant has different signature", 74, 74);
x_87 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_87);
return x_34;
}
}
else
{
uint8_t x_88; 
lean_free_object(x_34);
x_88 = lean_unbox(x_78);
x_21 = x_69;
x_22 = x_31;
x_23 = x_88;
x_24 = x_36;
goto block_30;
}
}
}
}
}
}
else
{
lean_object* x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_34, 1);
lean_inc(x_89);
lean_dec(x_34);
x_90 = l_Lean_ConstantKind_ofConstantInfo(x_31);
x_91 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_92 = l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230_(x_91, x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_1);
x_93 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: constant has kind ", 51, 51);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248_(x_90, x_94);
x_96 = lean_unsigned_to_nat(120u);
x_97 = lean_format_pretty(x_95, x_96, x_94, x_94);
x_98 = lean_string_append(x_93, x_97);
lean_dec(x_97);
x_99 = lean_mk_string_unchecked(" but expected ", 14, 14);
x_100 = lean_string_append(x_98, x_99);
lean_dec(x_99);
x_101 = l___private_Lean_Environment_0__Lean_reprConstantKind____x40_Lean_Environment___hyg_1248_(x_91, x_94);
x_102 = lean_format_pretty(x_101, x_96, x_94, x_94);
x_103 = lean_string_append(x_100, x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_89);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_106 = lean_ctor_get(x_1, 3);
lean_inc(x_106);
x_107 = l_IO_Promise_result_x21___redArg(x_106);
lean_dec(x_106);
x_108 = lean_task_get_own(x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
x_110 = l_Lean_ConstantInfo_levelParams(x_31);
x_111 = l_List_beq___at_____private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431__spec__0(x_109, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_108);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_1);
x_112 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: constant has level params ", 59, 59);
x_113 = l_List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0(x_110);
x_114 = lean_string_append(x_112, x_113);
lean_dec(x_113);
x_115 = lean_mk_string_unchecked(" but expected ", 14, 14);
x_116 = lean_string_append(x_114, x_115);
lean_dec(x_115);
x_117 = l_List_toString___at___Lean_Environment_AddConstAsyncResult_commitConst_spec__0(x_109);
x_118 = lean_string_append(x_116, x_117);
lean_dec(x_117);
x_119 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_89);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_110);
lean_dec(x_109);
x_121 = lean_ctor_get(x_108, 2);
lean_inc(x_121);
lean_dec(x_108);
x_122 = l_Lean_ConstantInfo_type(x_31);
x_123 = lean_expr_eqv(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_1);
x_124 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: constant has type ", 51, 51);
x_125 = lean_expr_dbg_to_string(x_122);
lean_dec(x_122);
x_126 = lean_string_append(x_124, x_125);
lean_dec(x_125);
x_127 = lean_mk_string_unchecked(" but expected ", 14, 14);
x_128 = lean_string_append(x_126, x_127);
lean_dec(x_127);
x_129 = lean_expr_dbg_to_string(x_121);
lean_dec(x_121);
x_130 = lean_string_append(x_128, x_129);
lean_dec(x_129);
x_131 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_89);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_122);
lean_dec(x_121);
x_133 = lean_box(0);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_134; 
lean_dec(x_33);
x_134 = lean_unbox(x_133);
x_21 = x_123;
x_22 = x_31;
x_23 = x_134;
x_24 = x_89;
goto block_30;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_4, 0);
lean_inc(x_135);
x_136 = l_Lean_ConstantInfo_toConstantVal(x_135);
lean_dec(x_135);
x_137 = l___private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431_(x_136, x_33);
lean_dec(x_33);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_31);
lean_dec(x_1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_138 = x_4;
} else {
 lean_dec_ref(x_4);
 x_138 = lean_box(0);
}
x_139 = lean_mk_string_unchecked("AddConstAsyncResult.commitConst: exported constant has different signature", 74, 74);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(18, 1, 0);
} else {
 x_140 = x_138;
 lean_ctor_set_tag(x_140, 18);
}
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_89);
return x_141;
}
else
{
uint8_t x_142; 
x_142 = lean_unbox(x_133);
x_21 = x_123;
x_22 = x_31;
x_23 = x_142;
x_24 = x_89;
goto block_30;
}
}
}
}
}
}
}
else
{
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_1);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_AddConstAsyncResult_commitConst(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
x_20 = l_IO_Promise_isResolved___redArg(x_19, x_3);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
lean_inc(x_1);
x_25 = l_Lean_Environment_AddConstAsyncResult_commitConst(x_1, x_2, x_24, x_24, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_4 = x_26;
goto block_18;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_4 = x_27;
goto block_18;
}
block_18:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_task_get_own(x_5);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
x_8 = lean_io_promise_resolve(x_6, x_7, x_4);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 7);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_task_get_own(x_10);
x_12 = lean_ctor_get(x_1, 6);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_io_promise_resolve(x_11, x_12, x_9);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_contains(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Environment_contains(x_1, x_2, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_containsOnBranch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Environment_0__Lean_Environment_asyncConsts(x_1);
x_8 = l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(x_7, x_2);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_3 = x_11;
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_3 = x_13;
goto block_6;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
return x_15;
}
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(x_4, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_containsOnBranch___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_containsOnBranch(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_header(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 5);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_header___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_header(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_imports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Environment_header(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_imports___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_imports(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_allImportedModuleNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Environment_header(x_1);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_allImportedModuleNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_allImportedModuleNames(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule_unsafe__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule_unsafe__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_setMainModule_unsafe__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_2, 4);
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_ctor_get_uint32(x_9, sizeof(void*)*5);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*5 + 4);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set_uint32(x_16, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 4, x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_17 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_6);
lean_ctor_set(x_17, 3, x_7);
lean_ctor_set(x_17, 4, x_8);
lean_ctor_set(x_17, 5, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*6, x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; 
x_3 = lean_alloc_closure((void*)(l_Lean_Environment_setMainModule___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 4);
lean_inc(x_9);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
x_10 = x_16;
goto block_15;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_16, 0, x_21);
x_10 = x_16;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_4);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_10 = x_26;
goto block_15;
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 7);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set(x_14, 4, x_9);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_11);
lean_ctor_set(x_14, 7, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*8, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setMainModule___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_setMainModule___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_mainModule(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Environment_header(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_mainModule___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_mainModule(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_25; 
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_26, 0);
x_3 = x_27;
goto block_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_28, 1);
x_3 = x_29;
goto block_24;
}
block_24:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = lean_unsigned_to_nat(32u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_shift_right(x_7, x_9);
x_11 = lean_uint64_xor(x_7, x_10);
x_12 = lean_unsigned_to_nat(16u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_sub(x_17, x_19);
x_21 = lean_usize_land(x_16, x_20);
x_22 = lean_array_uget(x_5, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_2, x_22);
lean_dec(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdxFor_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isImportedConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isImportedConst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_isImportedConst(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isConstructor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_3);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_9 = lean_box(6);
x_10 = lean_unbox(x_9);
x_11 = l___private_Lean_Environment_0__Lean_beqConstantKind____x40_Lean_Environment___hyg_1230_(x_8, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isConstructor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_isConstructor(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isSafeDefinition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_3);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_task_get_own(x_10);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
lean_dec(x_12);
x_14 = lean_box(x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = lean_unbox(x_3);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = lean_unbox(x_3);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_7);
x_19 = lean_unbox(x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isSafeDefinition___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_isSafeDefinition(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_getModuleIdx_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lean_Environment_getModuleIdx_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Environment_header(x_1);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_findIdx_x3f_loop___redArg(x_3, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_getModuleIdx_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getModuleIdx_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_getModuleIdx_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Expr_instantiateLevelParams(x_3, x_4, x_2);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_ConstantInfo_toConstantVal(x_1);
x_4 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_instantiateTypeLevelParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ConstantInfo_instantiateTypeLevelParams(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_ConstantInfo_value_x21(x_1, x_4);
x_6 = l_Lean_ConstantInfo_levelParams(x_1);
x_7 = l_Lean_Expr_instantiateLevelParams(x_5, x_6, x_2);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_EnvExtension_AsyncMode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ConstantKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_AsyncMode_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_EnvExtension_AsyncMode_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_AsyncMode_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_EnvExtension_AsyncMode_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_EnvExtension_instInhabitedAsyncMode() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtension___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("(`Inhabited.default` for `IO.Error`)", 36, 36);
x_3 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnvExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_instInhabitedEnvExtension___lam__0), 1, 0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_initFn____x40_Lean_Environment___hyg_6645_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_st_mk_ref(x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_ensureExtensionsArraySize_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l___private_Lean_Environment_0__Lean_EnvExtension_envExtensionsRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_free_object(x_5);
x_11 = lean_array_fget(x_7, x_1);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_1(x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_push(x_2, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_16;
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_array_get_size(x_24);
x_27 = lean_nat_dec_lt(x_1, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_24, x_1);
lean_dec(x_24);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_apply_1(x_30, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_array_push(x_2, x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_1, x_35);
lean_dec(x_1);
x_1 = x_36;
x_2 = x_34;
x_3 = x_33;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_40 = x_31;
} else {
 lean_dec_ref(x_31);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_ensureExtensionsArraySize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l_Lean_EnvExtension_ensureExtensionsArraySize_loop(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Environment_0__Lean_EnvExtension_invalidExtMsg() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid environment extension has been accessed", 47, 47);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Environment_0__Lean_EnvExtension_setStateImpl_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_7 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_8 = lean_mk_string_unchecked("_private.Lean.Environment.0.Lean.EnvExtension.setStateImpl", 58, 58);
x_9 = lean_unsigned_to_nat(1249u);
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_mk_string_unchecked("invalid environment extension has been accessed", 47, 47);
x_12 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_13 = l_panic___at_____private_Lean_Environment_0__Lean_EnvExtension_setStateImpl_spec__0(x_2, x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fset(x_2, x_4, x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_setStateImpl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_7 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_8 = lean_mk_string_unchecked("_private.Lean.Environment.0.Lean.EnvExtension.modifyStateImpl", 61, 61);
x_9 = lean_unsigned_to_nat(1260u);
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_mk_string_unchecked("invalid environment extension has been accessed", 47, 47);
x_12 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_panic_fn(x_2, x_12);
return x_13;
}
else
{
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_2, x_4);
x_15 = lean_box(0);
x_16 = lean_array_fset(x_2, x_4, x_15);
x_17 = lean_apply_1(x_3, x_14);
x_18 = lean_array_fset(x_16, x_4, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_8 = lean_mk_string_unchecked("_private.Lean.Environment.0.Lean.EnvExtension.getStateImpl", 58, 58);
x_9 = lean_unsigned_to_nat(1266u);
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_mk_string_unchecked("invalid environment extension has been accessed", 47, 47);
x_12 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_13 = l_panic___redArg(x_1, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_array_fget(x_3, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_EnvExtension_mkInitialExtStates_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_1(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_16;
x_3 = x_17;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_mkInitialExtStates(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; 
x_2 = l___private_Lean_Environment_0__Lean_EnvExtension_envExtensionsRef;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
x_9 = l_Array_mapMUnsafe_map___at___Lean_EnvExtension_mkInitialExtStates_spec__0(x_6, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_EnvExtension_mkInitialExtStates_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_EnvExtension_mkInitialExtStates_spec__0(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(x_1, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_modifyState_unsafe__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_modifyState_unsafe__1___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_modifyState_unsafe__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(x_1, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_modifyState_unsafe__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_modifyState_unsafe__2___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_modifyState_unsafe__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_modifyState_unsafe__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_modifyState_unsafe__3___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState_unsafe__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_modifyState_unsafe__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_EnvExtension_modifyState_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_inc(x_3);
x_8 = l_Lean_EnvExtension_modifyState_unsafe__3___redArg(x_1, x_2, x_3);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 5);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set(x_11, 5, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*6, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_4);
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
lean_inc(x_2);
x_12 = l_Lean_EnvExtension_modifyState_unsafe__2___redArg(x_1, x_2, x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_7, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 5);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*6, x_9);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 7);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set(x_26, 5, x_22);
lean_ctor_set(x_26, 6, x_23);
lean_ctor_set(x_26, 7, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*8, x_25);
return x_26;
}
case 2:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 4);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_29, sizeof(void*)*6);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
lean_inc(x_2);
x_34 = l_Lean_EnvExtension_modifyState_unsafe__1___redArg(x_1, x_2, x_3);
lean_dec(x_1);
x_35 = lean_ctor_get(x_29, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 5);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_31);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 6);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 7);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_41);
lean_ctor_set(x_47, 3, x_42);
lean_ctor_set(x_47, 4, x_27);
lean_ctor_set(x_47, 5, x_43);
lean_ctor_set(x_47, 6, x_44);
lean_ctor_set(x_47, 7, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*8, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_69; 
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_ctor_get(x_27, 0);
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_50 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_51 = lean_mk_string_unchecked("Lean.EnvExtension.modifyState", 29, 29);
x_52 = lean_unsigned_to_nat(1287u);
x_53 = lean_unsigned_to_nat(13u);
x_54 = lean_mk_string_unchecked("environment extension is marked as `mainOnly` but used in ", 58, 58);
x_69 = l_Lean_Environment_isRealizing(x_2);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_mk_string_unchecked("async", 5, 5);
x_55 = x_70;
goto block_68;
}
else
{
lean_object* x_71; 
x_71 = lean_mk_string_unchecked("realization", 11, 11);
x_55 = x_71;
goto block_68;
}
block_68:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_mk_string_unchecked(" context '", 10, 10);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = lean_ctor_get(x_48, 0);
lean_inc(x_59);
lean_dec(x_48);
x_60 = lean_box(1);
x_61 = lean_unbox(x_60);
x_62 = l_Lean_Name_toString(x_59, x_61, x_49);
x_63 = lean_string_append(x_58, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked("'", 1, 1);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_50, x_51, x_52, x_53, x_65);
lean_dec(x_65);
lean_dec(x_51);
lean_dec(x_50);
x_67 = l_panic___at___Lean_EnvExtension_modifyState_spec__0(x_2, x_66);
return x_67;
}
}
}
default: 
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
lean_inc(x_1);
x_72 = lean_alloc_closure((void*)(l_Lean_EnvExtension_modifyState___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_72, 0, x_1);
lean_closure_set(x_72, 1, x_3);
x_73 = lean_ctor_get(x_1, 2);
lean_inc(x_73);
lean_dec(x_1);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_2, 4);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_2, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_2, x_72);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_72);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_81 = lean_box(1);
x_82 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_83 = lean_mk_string_unchecked("Lean.EnvExtension.modifyState", 29, 29);
x_84 = lean_unsigned_to_nat(1295u);
x_85 = lean_unsigned_to_nat(15u);
x_86 = lean_mk_string_unchecked("environment extension must set `replay\?` field to be used in realization context '", 82, 82);
x_87 = lean_unbox(x_81);
x_88 = l_Lean_Name_toString(x_79, x_87, x_80);
x_89 = lean_string_append(x_86, x_88);
lean_dec(x_88);
x_90 = lean_mk_string_unchecked("'", 1, 1);
x_91 = lean_string_append(x_89, x_90);
lean_dec(x_90);
x_92 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_82, x_83, x_84, x_85, x_91);
lean_dec(x_91);
lean_dec(x_83);
lean_dec(x_82);
x_93 = l_panic___at___Lean_EnvExtension_modifyState_spec__0(x_2, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_73);
x_94 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_2, x_72);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_EnvExtension_modifyState___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_modifyState___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_EnvExtension_modifyState___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_modifyState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_EnvExtension_modifyState(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_inc(x_3);
x_8 = l_Lean_EnvExtension_modifyState_unsafe__3___redArg(x_1, x_2, x_3);
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 5);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set(x_11, 5, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*6, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_EnvExtension_setState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_box(x_5);
switch (lean_obj_tag(x_6)) {
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
lean_inc(x_2);
x_13 = l_Lean_EnvExtension_modifyState_unsafe__2___redArg(x_1, x_2, x_4);
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 5);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set(x_16, 5, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_10);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 7);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*8, x_26);
return x_27;
}
case 2:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 4);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_30, sizeof(void*)*6);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 2);
lean_inc(x_34);
lean_inc(x_2);
x_35 = l_Lean_EnvExtension_modifyState_unsafe__1___redArg(x_1, x_2, x_4);
lean_dec(x_1);
x_36 = lean_ctor_get(x_30, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 5);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
lean_ctor_set(x_38, 5, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*6, x_32);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 5);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 6);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 7);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
lean_dec(x_2);
x_48 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_41);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_43);
lean_ctor_set(x_48, 4, x_28);
lean_ctor_set(x_48, 5, x_44);
lean_ctor_set(x_48, 6, x_45);
lean_ctor_set(x_48, 7, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*8, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_70; 
lean_dec(x_4);
lean_dec(x_1);
x_49 = lean_ctor_get(x_28, 0);
lean_inc(x_49);
lean_dec(x_28);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_51 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_52 = lean_mk_string_unchecked("Lean.EnvExtension.modifyState", 29, 29);
x_53 = lean_unsigned_to_nat(1287u);
x_54 = lean_unsigned_to_nat(13u);
x_55 = lean_mk_string_unchecked("environment extension is marked as `mainOnly` but used in ", 58, 58);
x_70 = l_Lean_Environment_isRealizing(x_2);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_mk_string_unchecked("async", 5, 5);
x_56 = x_71;
goto block_69;
}
else
{
lean_object* x_72; 
x_72 = lean_mk_string_unchecked("realization", 11, 11);
x_56 = x_72;
goto block_69;
}
block_69:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_mk_string_unchecked(" context '", 10, 10);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
lean_dec(x_49);
x_61 = lean_box(1);
x_62 = lean_unbox(x_61);
x_63 = l_Lean_Name_toString(x_60, x_62, x_50);
x_64 = lean_string_append(x_59, x_63);
lean_dec(x_63);
x_65 = lean_mk_string_unchecked("'", 1, 1);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_51, x_52, x_53, x_54, x_66);
lean_dec(x_66);
lean_dec(x_52);
lean_dec(x_51);
x_68 = lean_panic_fn(x_2, x_67);
return x_68;
}
}
}
default: 
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_6);
lean_inc(x_1);
x_73 = lean_alloc_closure((void*)(l_Lean_EnvExtension_setState___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_73, 0, x_1);
lean_closure_set(x_73, 1, x_4);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
lean_dec(x_1);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_2, 4);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_2, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_2, x_73);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_73);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_82 = lean_box(1);
x_83 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_84 = lean_mk_string_unchecked("Lean.EnvExtension.modifyState", 29, 29);
x_85 = lean_unsigned_to_nat(1295u);
x_86 = lean_unsigned_to_nat(15u);
x_87 = lean_mk_string_unchecked("environment extension must set `replay\?` field to be used in realization context '", 82, 82);
x_88 = lean_unbox(x_82);
x_89 = l_Lean_Name_toString(x_80, x_88, x_81);
x_90 = lean_string_append(x_87, x_89);
lean_dec(x_89);
x_91 = lean_mk_string_unchecked("'", 1, 1);
x_92 = lean_string_append(x_90, x_91);
lean_dec(x_91);
x_93 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_83, x_84, x_85, x_86, x_92);
lean_dec(x_92);
lean_dec(x_84);
lean_dec(x_83);
x_94 = lean_panic_fn(x_2, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_74);
x_95 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_2, x_73);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_EnvExtension_setState___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtension_setState___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_EnvExtension_setState___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnvExtension_setState___redArg___lam__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_4);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_task_get_own(x_6);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_1, x_2, x_8);
lean_dec(x_8);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_10 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_11 = lean_mk_string_unchecked("_private.Lean.Environment.0.Lean.EnvExtension.getStateUnsafe", 60, 60);
x_12 = lean_unsigned_to_nat(1313u);
x_13 = lean_unsigned_to_nat(17u);
x_14 = lean_mk_string_unchecked("called on `async` extension, use `findStateAsync` instead or pass `(asyncMode := .local)` to explicitly access local state", 122, 122);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_16 = l_panic___redArg(x_1, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_1, x_2, x_19);
lean_dec(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe_findRecExts_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_3);
x_4 = l___private_Lean_Environment_0__Lean_AsyncConsts_findPrefix_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_3);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_10 = l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_task_get_own(x_11);
x_13 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_12, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_1 = x_4;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
return x_19;
}
}
else
{
lean_dec(x_1);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_6, 3);
x_8 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_2, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_36; 
x_13 = l_Lean_Name_instBEq;
x_14 = l_Lean_instHashableName;
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
x_16 = x_37;
goto block_35;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
x_16 = x_38;
goto block_35;
}
block_12:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___lam__0(x_3, x_1, x_2, x_7);
lean_dec(x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_task_get_own(x_9);
x_11 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_1, x_2, x_10);
lean_dec(x_10);
return x_11;
}
}
block_35:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_4);
x_18 = l_Lean_SMap_contains___redArg(x_13, x_14, x_17, x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_19 = l___private_Lean_Environment_0__Lean_Environment_asyncConsts(x_3);
x_20 = l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(x_19, x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_inc(x_4);
x_21 = l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe_findRecExts_x3f(x_20, x_19, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 7);
lean_inc(x_22);
x_23 = lean_task_get_own(x_22);
x_24 = l_Lean_NameMap_find_x3f(lean_box(0), x_23, x_4);
lean_dec(x_4);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___lam__0(x_3, x_1, x_2, x_25);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_5 = x_27;
goto block_12;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_task_get_own(x_28);
x_30 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_1, x_2, x_29);
lean_dec(x_29);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_4);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_5 = x_31;
goto block_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_1, x_2, x_33);
lean_dec(x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension_unsafe__1___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension_unsafe__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerEnvExtension_unsafe__1___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_registerEnvExtension_unsafe__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_initializing(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_mk_string_unchecked("failed to register environment, extensions can only be registered during initialization", 87, 87);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_mk_string_unchecked("failed to register environment, extensions can only be registered during initialization", 87, 87);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_Environment_0__Lean_EnvExtension_envExtensionsRef;
x_18 = lean_st_ref_get(x_17, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_17, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_19);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_1);
lean_ctor_set(x_25, 2, x_2);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_3);
lean_inc(x_25);
x_26 = lean_array_push(x_22, x_25);
x_27 = lean_st_ref_set(x_17, x_26, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerEnvExtension___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_registerEnvExtension___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_registerEnvExtension(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_mkInitialExtensionStates(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_EnvExtension_mkInitialExtStates(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_environment(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_io_initializing(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_EnvExtension_mkInitialExtStates(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(1);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_shiftl(x_11, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_nextPowerOfTwo(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unbox(x_10);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_21);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unbox(x_4);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_box(0);
x_29 = lean_box(0);
x_30 = lean_mk_empty_array_with_capacity(x_12);
lean_inc_n(x_30, 3);
x_31 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set_uint32(x_31, sizeof(void*)*5, x_1);
x_32 = lean_unbox(x_4);
lean_ctor_set_uint8(x_31, sizeof(void*)*5 + 4, x_32);
lean_inc(x_9);
x_33 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_20);
lean_ctor_set(x_33, 3, x_9);
lean_ctor_set(x_33, 4, x_28);
lean_ctor_set(x_33, 5, x_31);
x_34 = lean_unbox(x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_34);
lean_inc_n(x_33, 2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_task_pure(x_33);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = l_Lean_NameTrie_empty(lean_box(0));
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_box(0);
x_43 = lean_box(0);
x_44 = lean_task_pure(x_28);
x_45 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_9);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set(x_45, 5, x_43);
lean_ctor_set(x_45, 6, x_28);
lean_ctor_set(x_45, 7, x_44);
x_46 = lean_unbox(x_4);
lean_dec(x_4);
lean_ctor_set_uint8(x_45, sizeof(void*)*8, x_46);
lean_ctor_set(x_7, 0, x_45);
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_box(1);
x_50 = lean_unsigned_to_nat(8u);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_shiftl(x_50, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = l_Nat_nextPowerOfTwo(x_55);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = lean_mk_array(x_56, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_inc(x_59);
x_62 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_unbox(x_49);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_63);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_60);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_unbox(x_4);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_66);
x_67 = lean_box(0);
x_68 = lean_box(0);
x_69 = lean_mk_empty_array_with_capacity(x_51);
lean_inc_n(x_69, 3);
x_70 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set_uint32(x_70, sizeof(void*)*5, x_1);
x_71 = lean_unbox(x_4);
lean_ctor_set_uint8(x_70, sizeof(void*)*5 + 4, x_71);
lean_inc(x_47);
x_72 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_65);
lean_ctor_set(x_72, 2, x_59);
lean_ctor_set(x_72, 3, x_47);
lean_ctor_set(x_72, 4, x_67);
lean_ctor_set(x_72, 5, x_70);
x_73 = lean_unbox(x_4);
lean_ctor_set_uint8(x_72, sizeof(void*)*6, x_73);
lean_inc_n(x_72, 2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_task_pure(x_72);
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = l_Lean_NameTrie_empty(lean_box(0));
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_67);
lean_ctor_set(x_79, 3, x_78);
lean_inc(x_79);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_box(0);
x_82 = lean_box(0);
x_83 = lean_task_pure(x_67);
x_84 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_47);
lean_ctor_set(x_84, 2, x_75);
lean_ctor_set(x_84, 3, x_80);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set(x_84, 5, x_82);
lean_ctor_set(x_84, 6, x_67);
lean_ctor_set(x_84, 7, x_83);
x_85 = lean_unbox(x_4);
lean_dec(x_4);
lean_ctor_set_uint8(x_84, sizeof(void*)*8, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_48);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_7);
if (x_87 == 0)
{
return x_7;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_7, 0);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_7);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_4);
x_91 = !lean_is_exclusive(x_3);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_3, 0);
lean_dec(x_92);
x_93 = lean_mk_string_unchecked("environment objects cannot be created during initialization", 59, 59);
x_94 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_94);
return x_3;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
lean_dec(x_3);
x_96 = lean_mk_string_unchecked("environment objects cannot be created during initialization", 59, 59);
x_97 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkEmptyEnvironment___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_mk_empty_environment(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtensionState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("(`Inhabited.default` for `IO.Error`)", 36, 36);
x_3 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_mk_string_unchecked("(`Inhabited.default` for `IO.Error`)", 36, 36);
x_5 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lam__0), 1, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lam__1___boxed), 3, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_EnvExtension_setState___redArg___lam__0___boxed), 2, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lam__3___boxed), 1, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_instInhabitedPersistentEnvExtension___lam__2___boxed), 1, 0);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_unbox(x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_14);
x_15 = lean_box(0);
lean_inc(x_8);
x_16 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_7);
lean_ctor_set(x_16, 4, x_8);
lean_ctor_set(x_16, 5, x_8);
lean_ctor_set(x_16, 6, x_9);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPersistentEnvExtension___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedPersistentEnvExtension___lam__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___lam__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedPersistentEnvExtension___lam__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instInhabitedPersistentEnvExtension(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Array_instInhabited(lean_box(0));
x_6 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_6, x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_get(x_5, x_9, x_3);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_7, 3);
x_9 = l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___redArg(x_1, x_2, x_4, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 1);
x_11 = l_Lean_PersistentEnvExtension_getModuleEntries_unsafe__1___redArg(x_1, x_2, x_4, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_PersistentEnvExtension_getModuleEntries(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_apply_2(x_4, x_5, x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_addEntry___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_7 = l_Lean_EnvExtension_modifyState___redArg(x_5, x_2, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_5, x_6, x_3, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentEnvExtension_getState___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_PersistentEnvExtension_getState___redArg(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_getState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_PersistentEnvExtension_getState(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_setState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_7 = l_Lean_EnvExtension_modifyState___redArg(x_5, x_2, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentEnvExtension_setState___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_setState___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentEnvExtension_setState___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_PersistentEnvExtension_modifyState___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_EnvExtension_modifyState___redArg(x_6, x_2, x_5, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentEnvExtension_modifyState___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_PersistentEnvExtension_modifyState___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_modifyState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_PersistentEnvExtension_modifyState(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_findStateAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l___private_Lean_Environment_0__Lean_EnvExtension_findStateAsyncUnsafe___redArg(x_5, x_6, x_3, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_findStateAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentEnvExtension_findStateAsync___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_findStateAsync___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentEnvExtension_findStateAsync___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentEnvExtension_findStateAsync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentEnvExtension_findStateAsync(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_8540_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_st_mk_ref(x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_PersistentEnvExtensionDescr_name___autoParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_17 = lean_mk_string_unchecked("declName", 8, 8);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = lean_mk_string_unchecked("decl_name%", 10, 10);
x_20 = l_Lean_mkAtom(x_19);
lean_inc(x_7);
x_21 = lean_array_push(x_7, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_push(x_15, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_apply_4(x_1, x_7, x_8, x_4, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__0), 2, 0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_6);
x_48 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_49 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_50 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_51 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_52 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_53 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_54 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_49);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_56, 4, x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_58 = lean_nat_dec_lt(x_46, x_47);
if (x_58 == 0)
{
lean_dec(x_57);
lean_dec(x_47);
lean_free_object(x_4);
lean_dec(x_6);
goto block_45;
}
else
{
if (x_58 == 0)
{
lean_dec(x_57);
lean_dec(x_47);
lean_free_object(x_4);
lean_dec(x_6);
goto block_45;
}
else
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; uint8_t x_63; 
lean_inc(x_1);
x_59 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_59, 0, x_1);
x_60 = lean_usize_of_nat(x_46);
x_61 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_62 = l_Array_anyMUnsafe_any___redArg(x_57, x_59, x_6, x_60, x_61);
x_63 = lean_unbox(x_62);
if (x_63 == 0)
{
lean_dec(x_62);
lean_free_object(x_4);
goto block_45;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_8);
x_64 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed), 1, 0);
x_65 = lean_mk_string_unchecked("invalid environment extension, '", 32, 32);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
x_67 = lean_unbox(x_62);
lean_dec(x_62);
x_68 = l_Lean_Name_toString(x_66, x_67, x_64);
x_69 = lean_string_append(x_65, x_68);
lean_dec(x_68);
x_70 = lean_mk_string_unchecked("' has already been used", 23, 23);
x_71 = lean_string_append(x_69, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_72);
return x_4;
}
}
}
block_36:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_EStateM_bind), 7, 6);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, lean_box(0));
lean_closure_set(x_11, 3, lean_box(0));
lean_closure_set(x_11, 4, x_10);
lean_closure_set(x_11, 5, x_8);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_13 = l_Lean_registerEnvExtension___redArg(x_11, x_9, x_12, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 6);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set(x_25, 5, x_23);
lean_ctor_set(x_25, 6, x_24);
lean_inc(x_25);
x_26 = lean_array_push(x_17, x_25);
x_27 = lean_st_ref_set(x_3, x_26, x_18);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
block_45:
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_1, 7);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_9 = x_38;
goto block_36;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__1), 5, 1);
lean_closure_set(x_41, 0, x_40);
lean_ctor_set(x_37, 0, x_41);
x_9 = x_37;
goto block_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__1), 5, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_9 = x_44;
goto block_36;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_73 = lean_ctor_get(x_4, 0);
x_74 = lean_ctor_get(x_4, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_4);
x_75 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__0), 2, 0);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_array_get_size(x_73);
x_112 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_113 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_114 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_115 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_116 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_117 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_118 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_113);
x_120 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set(x_120, 2, x_115);
lean_ctor_set(x_120, 3, x_116);
lean_ctor_set(x_120, 4, x_117);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
x_122 = lean_nat_dec_lt(x_110, x_111);
if (x_122 == 0)
{
lean_dec(x_121);
lean_dec(x_111);
lean_dec(x_73);
goto block_109;
}
else
{
if (x_122 == 0)
{
lean_dec(x_121);
lean_dec(x_111);
lean_dec(x_73);
goto block_109;
}
else
{
lean_object* x_123; size_t x_124; size_t x_125; lean_object* x_126; uint8_t x_127; 
lean_inc(x_1);
x_123 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_123, 0, x_1);
x_124 = lean_usize_of_nat(x_110);
x_125 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_126 = l_Array_anyMUnsafe_any___redArg(x_121, x_123, x_73, x_124, x_125);
x_127 = lean_unbox(x_126);
if (x_127 == 0)
{
lean_dec(x_126);
goto block_109;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_75);
x_128 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed), 1, 0);
x_129 = lean_mk_string_unchecked("invalid environment extension, '", 32, 32);
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
lean_dec(x_1);
x_131 = lean_unbox(x_126);
lean_dec(x_126);
x_132 = l_Lean_Name_toString(x_130, x_131, x_128);
x_133 = lean_string_append(x_129, x_132);
lean_dec(x_132);
x_134 = lean_mk_string_unchecked("' has already been used", 23, 23);
x_135 = lean_string_append(x_133, x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_74);
return x_137;
}
}
}
block_102:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
x_78 = lean_alloc_closure((void*)(l_EStateM_bind), 7, 6);
lean_closure_set(x_78, 0, lean_box(0));
lean_closure_set(x_78, 1, lean_box(0));
lean_closure_set(x_78, 2, lean_box(0));
lean_closure_set(x_78, 3, lean_box(0));
lean_closure_set(x_78, 4, x_77);
lean_closure_set(x_78, 5, x_75);
x_79 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_80 = l_Lean_registerEnvExtension___redArg(x_78, x_76, x_79, x_74);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_take(x_3, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 6);
lean_inc(x_91);
lean_dec(x_1);
x_92 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_86);
lean_ctor_set(x_92, 2, x_87);
lean_ctor_set(x_92, 3, x_88);
lean_ctor_set(x_92, 4, x_89);
lean_ctor_set(x_92, 5, x_90);
lean_ctor_set(x_92, 6, x_91);
lean_inc(x_92);
x_93 = lean_array_push(x_84, x_92);
x_94 = lean_st_ref_set(x_3, x_93, x_85);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_1);
x_98 = lean_ctor_get(x_80, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_80, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_100 = x_80;
} else {
 lean_dec_ref(x_80);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
block_109:
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_1, 7);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_box(0);
x_76 = x_104;
goto block_102;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__1), 5, 1);
lean_closure_set(x_107, 0, x_105);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
x_76 = x_108;
goto block_102;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_registerPersistentEnvExtensionUnsafe(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_saveModuleDataParts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_save_module_data_parts(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_readModuleDataParts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_read_module_data_parts(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_saveModuleData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_array_push(x_7, x_5);
x_9 = lean_save_module_data_parts(x_2, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_saveModuleData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_saveModuleData(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_readModuleData_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_instInhabitedError;
x_4 = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_panic_fn(x_4, x_1);
x_6 = lean_apply_1(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_readModuleData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_array_push(x_4, x_1);
x_6 = lean_read_module_data_parts(x_5, x_2);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_array_get_size(x_8);
x_11 = lean_nat_dec_eq(x_10, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_free_object(x_6);
lean_dec(x_8);
x_12 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_13 = lean_mk_string_unchecked("Lean.readModuleData", 19, 19);
x_14 = lean_unsigned_to_nat(1598u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_mk_string_unchecked("assertion violation: parts.size == 1\n  ", 39, 39);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_readModuleData_spec__0(x_17, x_9);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_10);
lean_dec(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_6);
lean_dec(x_8);
x_21 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_22 = lean_mk_string_unchecked("Lean.readModuleData", 19, 19);
x_23 = lean_unsigned_to_nat(1599u);
x_24 = lean_unsigned_to_nat(31u);
x_25 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_26 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
x_27 = l_panic___at___Lean_readModuleData_spec__0(x_26, x_9);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_array_fget(x_8, x_19);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_eq(x_31, x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_29);
x_33 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_34 = lean_mk_string_unchecked("Lean.readModuleData", 19, 19);
x_35 = lean_unsigned_to_nat(1598u);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_mk_string_unchecked("assertion violation: parts.size == 1\n  ", 39, 39);
x_38 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_33, x_34, x_35, x_36, x_37);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
x_39 = l_panic___at___Lean_readModuleData_spec__0(x_38, x_30);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_lt(x_40, x_31);
lean_dec(x_31);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_29);
x_42 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_43 = lean_mk_string_unchecked("Lean.readModuleData", 19, 19);
x_44 = lean_unsigned_to_nat(1599u);
x_45 = lean_unsigned_to_nat(31u);
x_46 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_47 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_42, x_43, x_44, x_45, x_46);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_42);
x_48 = l_panic___at___Lean_readModuleData_spec__0(x_47, x_30);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_array_fget(x_29, x_40);
lean_dec(x_29);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_30);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
return x_6;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_6, 0);
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_6);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_freeRegions_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_compacted_region_free(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lean_environment_free_regions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = l_Lean_Environment_header(x_1);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_5);
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_freeRegions_spec__0(x_4, x_12, x_13, x_7, x_2);
lean_dec(x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_freeRegions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_freeRegions_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_OLeanLevel_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ConstantKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_OLeanLevel_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_OLeanLevel_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_OLeanLevel_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_OLeanLevel_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_eq(x_1, x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(2);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_OLeanLevel_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_OLeanLevel_toCtorIdx(x_1);
x_4 = l_Lean_OLeanLevel_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqOLeanLevel___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_instDecidableEqOLeanLevel(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_adjustFileName(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (x_2) {
case 0:
{
return x_1;
}
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("server", 6, 6);
x_4 = l_System_FilePath_addExtension(x_1, x_3);
lean_dec(x_3);
return x_4;
}
default: 
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("private", 7, 7);
x_6 = l_System_FilePath_addExtension(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_OLeanLevel_adjustFileName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_OLeanLevel_adjustFileName(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_looksLikeOldCodegenName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; uint8_t x_3; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_2 = lean_ctor_get(x_1, 1);
x_15 = lean_mk_string_unchecked("_cstage", 7, 7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_byte_size(x_2);
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_unsigned_to_nat(7u);
x_20 = l_Substring_nextn(x_18, x_19, x_16);
lean_inc(x_2);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_string_utf8_byte_size(x_15);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Substring_beq(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_mk_string_unchecked("_spec_", 6, 6);
x_26 = lean_unsigned_to_nat(6u);
x_27 = l_Substring_nextn(x_18, x_26, x_16);
lean_dec(x_18);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_16);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_string_utf8_byte_size(x_25);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Substring_beq(x_28, x_30);
x_3 = x_31;
goto block_14;
}
else
{
lean_dec(x_18);
x_3 = x_24;
goto block_14;
}
block_14:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_mk_string_unchecked("_elambda", 8, 8);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_2);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_unsigned_to_nat(8u);
x_9 = l_Substring_nextn(x_7, x_8, x_5);
lean_dec(x_7);
lean_inc(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_string_utf8_byte_size(x_4);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Substring_beq(x_10, x_12);
return x_13;
}
else
{
return x_3;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_box(0);
x_33 = lean_unbox(x_32);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_looksLikeOldCodegenName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Environment_0__Lean_looksLikeOldCodegenName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__0(lean_object* x_1, uint8_t x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_18; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_7 = l_Lean_instInhabitedEnvExtensionState;
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*3);
lean_dec(x_31);
x_33 = lean_box(x_32);
if (lean_obj_tag(x_33) == 3)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
x_18 = x_35;
goto block_30;
}
else
{
lean_dec(x_33);
x_18 = x_32;
goto block_30;
}
block_17:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_4, x_13);
x_15 = lean_array_uset(x_10, x_4, x_11);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
block_30:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
lean_inc(x_1);
x_19 = l_Lean_PersistentEnvExtension_getState___redArg(x_7, x_8, x_1, x_18);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_instDecidableEqOLeanLevel(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 5);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_apply_1(x_24, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_11 = x_26;
goto block_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 4);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_apply_1(x_27, x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_11 = x_29;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_ConstantInfo_name(x_5);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at___Lean_mkModuleData_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at___Lean_mkModuleData_spec__2_spec__2(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at___Lean_mkModuleData_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at___Lean_mkModuleData_spec__2_spec__2(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_mkModuleData_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_13; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_4, x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_3, x_4);
lean_inc(x_18);
lean_inc(x_1);
x_19 = l_Lean_Environment_find_x3f(x_1, x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = l___private_Lean_Environment_0__Lean_looksLikeOldCodegenName(x_18);
if (x_20 == 0)
{
lean_dec(x_18);
x_13 = x_19;
goto block_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_2);
x_21 = lean_elab_environment_to_kernel_env(x_2);
x_22 = lean_environment_find(x_21, x_18);
x_13 = x_22;
goto block_16;
}
}
else
{
lean_dec(x_18);
x_13 = x_19;
goto block_16;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
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
block_16:
{
if (lean_obj_tag(x_13) == 0)
{
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_array_push(x_6, x_14);
x_7 = x_15;
goto block_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_mkModuleData_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_nat_dec_lt(x_4, x_5);
if (x_8 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_le(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_4);
x_12 = lean_usize_of_nat(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_mkModuleData_spec__4_spec__4(x_1, x_2, x_3, x_11, x_12, x_7);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleData___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleData___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleData(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_46; uint8_t x_47; 
x_4 = l_Lean_persistentEnvExtensionsRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_alloc_closure((void*)(l_Lean_mkModuleData___lam__0___boxed), 3, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_mkModuleData___lam__1___boxed), 3, 0);
x_11 = l_Lean_Name_instBEq;
x_12 = l_Lean_instHashableName;
x_13 = lean_array_size(x_6);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
lean_inc(x_1);
x_16 = l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__0(x_1, x_2, x_13, x_15, x_6);
lean_inc(x_1);
x_31 = lean_elab_environment_to_kernel_env(x_1);
x_32 = lean_box(2);
x_46 = lean_unbox(x_32);
x_47 = l_Lean_instDecidableEqOLeanLevel(x_2, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_box(1);
x_49 = lean_unbox(x_48);
x_33 = x_49;
goto block_45;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_33 = x_51;
goto block_45;
}
block_30:
{
size_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_array_size(x_18);
lean_inc(x_18);
x_20 = l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__1(x_19, x_15, x_18);
x_21 = l_Lean_Environment_header(x_17);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*5 + 4);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_task_get_own(x_24);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_RBTree_toArray___at___Lean_mkModuleData_spec__2(x_26);
x_28 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_18);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_16);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_22);
if (lean_is_scalar(x_8)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_8;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
block_45:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; 
x_34 = l_Lean_Environment_setExporting(x_1, x_33);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unbox(x_32);
x_38 = l_Lean_instDecidableEqOLeanLevel(x_2, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_10);
x_39 = lean_mk_empty_array_with_capacity(x_14);
x_40 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_11, x_12, lean_box(0), lean_box(0), x_36, x_9, x_39);
lean_dec(x_36);
x_41 = lean_array_get_size(x_40);
lean_inc(x_34);
x_42 = l_Array_filterMapM___at___Lean_mkModuleData_spec__4(x_34, x_1, x_40, x_14, x_41);
lean_dec(x_41);
lean_dec(x_40);
x_17 = x_34;
x_18 = x_42;
goto block_30;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_1);
x_43 = lean_mk_empty_array_with_capacity(x_14);
x_44 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_11, x_12, lean_box(0), lean_box(0), x_36, x_10, x_43);
lean_dec(x_36);
x_17 = x_34;
x_18 = x_44;
goto block_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__0(x_1, x_6, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_mkModuleData_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_mkModuleData_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_mkModuleData_spec__4_spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_mkModuleData_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterMapM___at___Lean_mkModuleData_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleData___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkModuleData___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleData___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkModuleData___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_mkModuleData(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_writeModule___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_mkModuleData(x_1, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_OLeanLevel_adjustFileName(x_2, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = l_Lean_OLeanLevel_adjustFileName(x_2, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_writeModule(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Environment_header(x_1);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_box(2);
x_7 = lean_unbox(x_6);
lean_inc(x_1);
x_8 = l_Lean_mkModuleData(x_1, x_7, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Environment_mainModule(x_1);
lean_dec(x_1);
x_12 = l_Lean_saveModuleData(x_2, x_11, x_9, x_10);
lean_dec(x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_writeModule___lam__0(x_1, x_2, x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_writeModule___lam__0(x_1, x_2, x_19, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(2);
x_24 = lean_unbox(x_23);
lean_inc(x_1);
x_25 = l_Lean_writeModule___lam__0(x_1, x_2, x_24, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Environment_mainModule(x_1);
lean_dec(x_1);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_31 = lean_array_push(x_30, x_16);
x_32 = lean_array_push(x_31, x_21);
x_33 = lean_array_push(x_32, x_26);
x_34 = lean_save_module_data_parts(x_28, x_33, x_27);
lean_dec(x_28);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_writeModule___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_writeModule___lam__0(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_nat_dec_lt(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; size_t x_30; lean_object* x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_array_fget(x_1, x_4);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_array_get_size(x_16);
x_20 = l_Lean_Name_hash___override(x_18);
x_21 = lean_unsigned_to_nat(32u);
x_22 = lean_uint64_of_nat(x_21);
x_23 = lean_uint64_shift_right(x_20, x_22);
x_24 = lean_uint64_xor(x_20, x_23);
x_25 = lean_unsigned_to_nat(16u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_shift_right(x_24, x_26);
x_28 = lean_uint64_xor(x_24, x_27);
x_29 = lean_uint64_to_usize(x_28);
x_30 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_sub(x_30, x_32);
x_34 = lean_usize_land(x_29, x_33);
x_35 = lean_array_uget(x_16, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_18, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_37 = lean_nat_add(x_15, x_31);
lean_dec(x_15);
lean_inc(x_4);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_4);
lean_ctor_set(x_38, 2, x_35);
x_39 = lean_array_uset(x_16, x_34, x_38);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_nat_shiftl(x_37, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_39);
lean_ctor_set(x_3, 1, x_46);
lean_ctor_set(x_3, 0, x_37);
x_6 = x_3;
goto block_10;
}
else
{
lean_ctor_set(x_3, 1, x_39);
lean_ctor_set(x_3, 0, x_37);
x_6 = x_3;
goto block_10;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_box(0);
x_48 = lean_array_uset(x_16, x_34, x_47);
lean_inc(x_4);
x_49 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_18, x_4, x_35);
x_50 = lean_array_uset(x_48, x_34, x_49);
lean_ctor_set(x_3, 1, x_50);
x_6 = x_3;
goto block_10;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; size_t x_65; size_t x_66; lean_object* x_67; size_t x_68; size_t x_69; size_t x_70; lean_object* x_71; uint8_t x_72; 
x_51 = lean_ctor_get(x_3, 0);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_3);
x_53 = lean_array_fget(x_1, x_4);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_array_get_size(x_52);
x_56 = l_Lean_Name_hash___override(x_54);
x_57 = lean_unsigned_to_nat(32u);
x_58 = lean_uint64_of_nat(x_57);
x_59 = lean_uint64_shift_right(x_56, x_58);
x_60 = lean_uint64_xor(x_56, x_59);
x_61 = lean_unsigned_to_nat(16u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_uint64_to_usize(x_64);
x_66 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_usize_of_nat(x_67);
x_69 = lean_usize_sub(x_66, x_68);
x_70 = lean_usize_land(x_65, x_69);
x_71 = lean_array_uget(x_52, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_54, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_73 = lean_nat_add(x_51, x_67);
lean_dec(x_51);
lean_inc(x_4);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set(x_74, 1, x_4);
lean_ctor_set(x_74, 2, x_71);
x_75 = lean_array_uset(x_52, x_70, x_74);
x_76 = lean_unsigned_to_nat(2u);
x_77 = lean_nat_shiftl(x_73, x_76);
x_78 = lean_unsigned_to_nat(3u);
x_79 = lean_nat_div(x_77, x_78);
lean_dec(x_77);
x_80 = lean_array_get_size(x_75);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_73);
lean_ctor_set(x_83, 1, x_82);
x_6 = x_83;
goto block_10;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_75);
x_6 = x_84;
goto block_10;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_box(0);
x_86 = lean_array_uset(x_52, x_70, x_85);
lean_inc(x_4);
x_87 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_54, x_4, x_71);
x_88 = lean_array_uset(x_86, x_70, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_51);
lean_ctor_set(x_89, 1, x_88);
x_6 = x_89;
goto block_10;
}
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_3 = x_6;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkExtNameMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_unsigned_to_nat(8u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_shiftl(x_8, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = l_Nat_nextPowerOfTwo(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_mk_array(x_14, x_15);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_9);
x_17 = lean_array_get_size(x_6);
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___redArg(x_6, x_19, x_4, x_1, x_7);
lean_dec(x_19);
lean_dec(x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_unsigned_to_nat(8u);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_shiftl(x_23, x_25);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_div(x_26, x_27);
lean_dec(x_26);
x_29 = l_Nat_nextPowerOfTwo(x_28);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_get_size(x_21);
x_34 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___redArg(x_21, x_35, x_32, x_1, x_22);
lean_dec(x_35);
lean_dec(x_21);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_mkExtNameMap_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_mk_array(x_3, x_5);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_set(x_4, x_1, x_2);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = l_Lean_instInhabitedEnvExtensionState;
x_8 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_7);
x_9 = lean_array_get(x_8, x_1, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(x_10, x_4, x_6);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_array_uget(x_9, x_4);
lean_inc(x_1);
x_11 = l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__1(x_1, x_10, x_5);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_18 = lean_array_uget(x_4, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash___override(x_19);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_sub(x_33, x_35);
x_37 = lean_usize_land(x_32, x_36);
x_38 = lean_array_uget(x_21, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_19, x_38);
lean_dec(x_38);
lean_dec(x_19);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_20);
x_9 = x_7;
x_10 = x_8;
goto block_15;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_3);
x_41 = l___private_Lean_Environment_0__Lean_setImportedEntries_unsafe__2(x_2, x_3, x_20, x_7, x_40);
lean_dec(x_40);
x_9 = x_41;
x_10 = x_8;
goto block_15;
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_6, x_12);
x_6 = x_13;
x_7 = x_9;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_nat_dec_lt(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_array_fget(x_1, x_6);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
lean_inc(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__1(x_2, x_3, x_6, x_12, x_13, x_15, x_5, x_7);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_5 = x_17;
x_6 = x_20;
x_7 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_nat_dec_lt(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_array_fget(x_3, x_6);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
lean_inc(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__1(x_1, x_2, x_6, x_12, x_13, x_15, x_5, x_7);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_21 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___redArg(x_3, x_1, x_2, x_4, x_17, x_20, x_18);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_setImportedEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_Lean_persistentEnvExtensionsRef;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_get_size(x_7);
lean_inc(x_3);
lean_inc(x_7);
x_10 = l_Array_toSubarray___redArg(x_7, x_3, x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
lean_inc(x_2);
x_15 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__0(x_2, x_10, x_12, x_14, x_1, x_8);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_mkExtNameMap(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_2);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___redArg(x_19, x_7, x_2, x_24, x_16, x_21, x_20);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_7);
lean_dec(x_19);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__1(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Environment_0__Lean_setImportedEntries_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_update_env_attributes(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_num_attributes(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*6, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_EnvExtension_ensureExtensionsArraySize(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_1, x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_persistentEnvExtensionsRef;
x_13 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lam__0(x_12, x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_free_object(x_13);
x_19 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lam__0(x_12, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_get_num_attributes(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_instInhabitedEnvExtensionState;
x_27 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_26);
x_28 = lean_box(1);
x_29 = lean_array_fget(x_15, x_3);
lean_dec(x_15);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_28);
lean_inc(x_4);
x_32 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_27, x_30, x_4, x_31);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_2);
lean_inc(x_4);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_4);
lean_inc(x_34);
x_35 = lean_apply_3(x_33, x_34, x_19, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_EnvExtension_setState___redArg(x_30, x_4, x_38);
x_40 = l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize(x_39, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_12, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_get_num_attributes(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_69; uint8_t x_70; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_array_get_size(x_21);
lean_dec(x_21);
x_69 = lean_array_get_size(x_44);
lean_dec(x_44);
x_70 = lean_nat_dec_lt(x_49, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = lean_nat_dec_lt(x_24, x_47);
lean_dec(x_47);
lean_dec(x_24);
x_50 = x_71;
goto block_68;
}
else
{
lean_dec(x_47);
lean_dec(x_24);
x_50 = x_70;
goto block_68;
}
block_68:
{
if (x_50 == 0)
{
lean_dec(x_49);
x_6 = x_41;
x_7 = x_48;
goto block_11;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_inc(x_1);
x_54 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_53, x_1, x_49, x_48);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_52, sizeof(void*)*6);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 5);
lean_inc(x_62);
lean_dec(x_52);
x_63 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_55);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*6, x_58);
x_64 = l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(x_41, x_63);
lean_dec(x_41);
x_65 = lean_update_env_attributes(x_64, x_56);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_6 = x_66;
x_7 = x_67;
goto block_11;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_65;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_46);
if (x_72 == 0)
{
return x_46;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
x_74 = lean_ctor_get(x_46, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_46);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_40;
}
}
else
{
uint8_t x_76; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_35);
if (x_76 == 0)
{
return x_35;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_35, 0);
x_78 = lean_ctor_get(x_35, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_35);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_19);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_23);
if (x_80 == 0)
{
return x_23;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_23, 0);
x_82 = lean_ctor_get(x_23, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_23);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_19, 0);
x_85 = lean_ctor_get(x_19, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_19);
x_86 = lean_get_num_attributes(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_instInhabitedEnvExtensionState;
x_90 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_89);
x_91 = lean_box(1);
x_92 = lean_array_fget(x_15, x_3);
lean_dec(x_15);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_91);
lean_inc(x_4);
x_95 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_90, x_93, x_4, x_94);
x_96 = lean_ctor_get(x_92, 2);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_2);
lean_inc(x_4);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_4);
lean_ctor_set(x_98, 1, x_2);
lean_inc(x_97);
x_99 = lean_apply_3(x_96, x_97, x_98, x_88);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_97);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_EnvExtension_setState___redArg(x_93, x_4, x_102);
x_104 = l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize(x_103, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_st_ref_get(x_12, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_get_num_attributes(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_133; uint8_t x_134; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_array_get_size(x_84);
lean_dec(x_84);
x_133 = lean_array_get_size(x_108);
lean_dec(x_108);
x_134 = lean_nat_dec_lt(x_113, x_133);
lean_dec(x_133);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = lean_nat_dec_lt(x_87, x_111);
lean_dec(x_111);
lean_dec(x_87);
x_114 = x_135;
goto block_132;
}
else
{
lean_dec(x_111);
lean_dec(x_87);
x_114 = x_134;
goto block_132;
}
block_132:
{
if (x_114 == 0)
{
lean_dec(x_113);
x_6 = x_105;
x_7 = x_112;
goto block_11;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_115 = lean_ctor_get(x_105, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_ctor_get(x_116, 3);
lean_inc(x_117);
lean_inc(x_1);
x_118 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_117, x_1, x_113, x_112);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_116, sizeof(void*)*6);
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_116, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_116, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 5);
lean_inc(x_126);
lean_dec(x_116);
x_127 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_127, 0, x_121);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set(x_127, 2, x_124);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set(x_127, 4, x_125);
lean_ctor_set(x_127, 5, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*6, x_122);
x_128 = l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(x_105, x_127);
lean_dec(x_105);
x_129 = lean_update_env_attributes(x_128, x_120);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_6 = x_130;
x_7 = x_131;
goto block_11;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_129;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_110, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_110, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_138 = x_110;
} else {
 lean_dec_ref(x_110);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_104;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_97);
lean_dec(x_93);
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = lean_ctor_get(x_99, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_99, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_142 = x_99;
} else {
 lean_dec_ref(x_99);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_84);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_86, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_86, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_146 = x_86;
} else {
 lean_dec_ref(x_86);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_13, 0);
x_149 = lean_ctor_get(x_13, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_13);
x_150 = lean_array_get_size(x_148);
x_151 = lean_nat_dec_lt(x_3, x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_148);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_4);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lam__0(x_12, x_149);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_get_num_attributes(x_155);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_instInhabitedEnvExtensionState;
x_161 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_160);
x_162 = lean_box(1);
x_163 = lean_array_fget(x_148, x_3);
lean_dec(x_148);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_unbox(x_162);
lean_inc(x_4);
x_166 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_161, x_164, x_4, x_165);
x_167 = lean_ctor_get(x_163, 2);
lean_inc(x_167);
lean_dec(x_163);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_2);
lean_inc(x_4);
if (lean_is_scalar(x_156)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_156;
}
lean_ctor_set(x_169, 0, x_4);
lean_ctor_set(x_169, 1, x_2);
lean_inc(x_168);
x_170 = lean_apply_3(x_167, x_168, x_169, x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_171);
x_174 = l_Lean_EnvExtension_setState___redArg(x_164, x_4, x_173);
x_175 = l___private_Lean_Environment_0__Lean_ensureExtensionsArraySize(x_174, x_172);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_st_ref_get(x_12, x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_get_num_attributes(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_204; uint8_t x_205; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_array_get_size(x_154);
lean_dec(x_154);
x_204 = lean_array_get_size(x_179);
lean_dec(x_179);
x_205 = lean_nat_dec_lt(x_184, x_204);
lean_dec(x_204);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = lean_nat_dec_lt(x_158, x_182);
lean_dec(x_182);
lean_dec(x_158);
x_185 = x_206;
goto block_203;
}
else
{
lean_dec(x_182);
lean_dec(x_158);
x_185 = x_205;
goto block_203;
}
block_203:
{
if (x_185 == 0)
{
lean_dec(x_184);
x_6 = x_176;
x_7 = x_183;
goto block_11;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_186 = lean_ctor_get(x_176, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_ctor_get(x_187, 3);
lean_inc(x_188);
lean_inc(x_1);
x_189 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_188, x_1, x_184, x_183);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_187, 0);
lean_inc(x_192);
x_193 = lean_ctor_get_uint8(x_187, sizeof(void*)*6);
x_194 = lean_ctor_get(x_187, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_187, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_187, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_187, 5);
lean_inc(x_197);
lean_dec(x_187);
x_198 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_190);
lean_ctor_set(x_198, 4, x_196);
lean_ctor_set(x_198, 5, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*6, x_193);
x_199 = l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(x_176, x_198);
lean_dec(x_176);
x_200 = lean_update_env_attributes(x_199, x_191);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_6 = x_201;
x_7 = x_202;
goto block_11;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_200;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_158);
lean_dec(x_154);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_181, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_181, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_209 = x_181;
} else {
 lean_dec_ref(x_181);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_dec(x_158);
lean_dec(x_154);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_175;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_168);
lean_dec(x_164);
lean_dec(x_158);
lean_dec(x_154);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_211 = lean_ctor_get(x_170, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_170, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_213 = x_170;
} else {
 lean_dec_ref(x_170);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_148);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_215 = lean_ctor_get(x_157, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_157, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_217 = x_157;
} else {
 lean_dec_ref(x_157);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_3 = x_9;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions_loop(x_2, x_3, x_5, x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_11; uint8_t x_12; lean_object* x_15; uint8_t x_16; 
x_2 = lean_ctor_get(x_1, 1);
x_11 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_11, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_array_fget(x_2, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*5);
lean_dec(x_19);
if (x_20 == 0)
{
x_12 = x_20;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_12 = x_22;
goto block_14;
}
}
block_10:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
block_14:
{
if (x_12 == 0)
{
x_3 = x_11;
goto block_10;
}
else
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(2u);
x_3 = x_13;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_publicModule_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_publicModule_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Environment_0__Lean_ImportedModule_publicModule_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_serverData_x3f(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_12; uint8_t x_13; lean_object* x_16; uint8_t x_17; 
x_3 = lean_ctor_get(x_1, 1);
x_12 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_3);
x_17 = lean_nat_dec_lt(x_12, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_fget(x_3, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*5);
lean_dec(x_20);
if (x_21 == 0)
{
x_13 = x_21;
goto block_15;
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_instDecidableEqOLeanLevel(x_2, x_23);
if (x_24 == 0)
{
x_13 = x_21;
goto block_15;
}
else
{
x_4 = x_12;
goto block_11;
}
}
}
block_11:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
block_15:
{
if (x_13 == 0)
{
x_4 = x_12;
goto block_11;
}
else
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(1u);
x_4 = x_14;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_ImportedModule_serverData_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Environment_0__Lean_ImportedModule_serverData_x3f(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
x_5 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
x_6 = lean_unsigned_to_nat(138u);
x_7 = lean_unsigned_to_nat(11u);
x_8 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_panic_fn(x_1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_name_eq(x_11, x_2);
if (x_14 == 0)
{
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_12);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAlreadyImported___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get(x_10, x_12, x_3);
x_14 = lean_array_get_size(x_7);
x_15 = l_Lean_Name_hash___override(x_4);
x_16 = lean_unsigned_to_nat(32u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_unsigned_to_nat(16u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_sub(x_25, x_27);
x_29 = lean_usize_land(x_24, x_28);
x_30 = lean_array_uget(x_7, x_29);
lean_dec(x_7);
x_31 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_11, x_4, x_30);
lean_dec(x_30);
x_32 = lean_array_get(x_10, x_12, x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked("import ", 7, 7);
x_34 = lean_box(1);
x_35 = lean_unbox(x_34);
lean_inc(x_9);
x_36 = l_Lean_Name_toString(x_13, x_35, x_9);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(" failed, environment already contains '", 39, 39);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_unbox(x_34);
lean_inc(x_9);
x_41 = l_Lean_Name_toString(x_4, x_40, x_9);
x_42 = lean_string_append(x_39, x_41);
lean_dec(x_41);
x_43 = lean_mk_string_unchecked("' from ", 7, 7);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = lean_unbox(x_34);
x_46 = l_Lean_Name_toString(x_32, x_45, x_9);
x_47 = lean_string_append(x_44, x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_5);
lean_ctor_set(x_2, 0, x_48);
return x_2;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; size_t x_65; size_t x_66; lean_object* x_67; size_t x_68; size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
lean_dec(x_2);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_51 = lean_box(0);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_ctor_get(x_1, 1);
x_54 = lean_array_get(x_51, x_53, x_3);
x_55 = lean_array_get_size(x_49);
x_56 = l_Lean_Name_hash___override(x_4);
x_57 = lean_unsigned_to_nat(32u);
x_58 = lean_uint64_of_nat(x_57);
x_59 = lean_uint64_shift_right(x_56, x_58);
x_60 = lean_uint64_xor(x_56, x_59);
x_61 = lean_unsigned_to_nat(16u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_uint64_to_usize(x_64);
x_66 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_usize_of_nat(x_67);
x_69 = lean_usize_sub(x_66, x_68);
x_70 = lean_usize_land(x_65, x_69);
x_71 = lean_array_uget(x_49, x_70);
lean_dec(x_49);
x_72 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_52, x_4, x_71);
lean_dec(x_71);
x_73 = lean_array_get(x_51, x_53, x_72);
lean_dec(x_72);
x_74 = lean_mk_string_unchecked("import ", 7, 7);
x_75 = lean_box(1);
x_76 = lean_unbox(x_75);
lean_inc(x_50);
x_77 = l_Lean_Name_toString(x_54, x_76, x_50);
x_78 = lean_string_append(x_74, x_77);
lean_dec(x_77);
x_79 = lean_mk_string_unchecked(" failed, environment already contains '", 39, 39);
x_80 = lean_string_append(x_78, x_79);
lean_dec(x_79);
x_81 = lean_unbox(x_75);
lean_inc(x_50);
x_82 = l_Lean_Name_toString(x_4, x_81, x_50);
x_83 = lean_string_append(x_80, x_82);
lean_dec(x_82);
x_84 = lean_mk_string_unchecked("' from ", 7, 7);
x_85 = lean_string_append(x_83, x_84);
lean_dec(x_84);
x_86 = lean_unbox(x_75);
x_87 = l_Lean_Name_toString(x_73, x_86, x_50);
x_88 = lean_string_append(x_85, x_87);
lean_dec(x_87);
x_89 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_5);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAlreadyImported(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwAlreadyImported___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAlreadyImported___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwAlreadyImported___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAlreadyImported___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwAlreadyImported(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportStateM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_mk_ref(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_8 = lean_apply_2(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_9);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_4, 1, x_14);
lean_ctor_set(x_4, 0, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_4);
lean_dec(x_6);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
lean_inc(x_21);
x_23 = lean_apply_2(x_1, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_21, x_25);
lean_dec(x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_34 = x_23;
} else {
 lean_dec_ref(x_23);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportStateM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_9 = lean_apply_2(x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_10);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_5);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
lean_inc(x_22);
x_24 = lean_apply_2(x_2, x_22, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_22, x_26);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_35 = x_24;
} else {
 lean_dec_ref(x_24);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_push(x_3, x_5);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_array_push(x_6, x_8);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
if (lean_obj_tag(x_10) == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_push(x_9, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_findOLeanParts___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_findOLeanParts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_findOLean(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_System_FilePath_pathExists(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_findOLeanParts___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_7);
x_12 = lean_mk_string_unchecked("object file '", 13, 13);
x_13 = lean_string_append(x_12, x_4);
lean_dec(x_4);
x_14 = lean_mk_string_unchecked("' of module ", 12, 12);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Name_toString(x_1, x_17, x_11);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(" does not exist", 15, 15);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_findOLeanParts___lam__0___boxed), 2, 1);
lean_closure_set(x_24, 0, x_7);
x_25 = lean_mk_string_unchecked("object file '", 13, 13);
x_26 = lean_string_append(x_25, x_4);
lean_dec(x_4);
x_27 = lean_mk_string_unchecked("' of module ", 12, 12);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Name_toString(x_1, x_30, x_24);
x_32 = lean_string_append(x_28, x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked(" does not exist", 15, 15);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_1);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_dec(x_6);
x_38 = lean_box(1);
x_39 = lean_unbox(x_38);
lean_inc(x_4);
x_40 = l_Lean_OLeanLevel_adjustFileName(x_4, x_39);
x_41 = l_System_FilePath_pathExists(x_40, x_37);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_mk_empty_array_with_capacity(x_45);
lean_inc(x_4);
x_47 = lean_array_push(x_46, x_4);
x_48 = lean_unbox(x_43);
lean_dec(x_43);
if (x_48 == 0)
{
lean_dec(x_40);
lean_dec(x_4);
lean_ctor_set(x_41, 0, x_47);
return x_41;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_free_object(x_41);
x_49 = lean_box(2);
x_50 = lean_unbox(x_49);
x_51 = l_Lean_OLeanLevel_adjustFileName(x_4, x_50);
x_52 = l_System_FilePath_pathExists(x_51, x_44);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_array_push(x_47, x_40);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
if (x_56 == 0)
{
lean_dec(x_51);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_57; 
x_57 = lean_array_push(x_55, x_51);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_array_push(x_47, x_40);
x_61 = lean_unbox(x_58);
lean_dec(x_58);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_51);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_array_push(x_60, x_51);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_41, 0);
x_66 = lean_ctor_get(x_41, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_41);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_mk_empty_array_with_capacity(x_67);
lean_inc(x_4);
x_69 = lean_array_push(x_68, x_4);
x_70 = lean_unbox(x_65);
lean_dec(x_65);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_40);
lean_dec(x_4);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_box(2);
x_73 = lean_unbox(x_72);
x_74 = l_Lean_OLeanLevel_adjustFileName(x_4, x_73);
x_75 = l_System_FilePath_pathExists(x_74, x_66);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_array_push(x_69, x_40);
x_80 = lean_unbox(x_76);
lean_dec(x_76);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_74);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_array_push(x_79, x_74);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_3);
if (x_84 == 0)
{
return x_3;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_3, 0);
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_3);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_findOLeanParts___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Environment_0__Lean_findOLeanParts___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_importModulesCore_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_instMonadEIO(lean_box(0));
x_5 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_4);
x_6 = lean_box(0);
x_7 = l_instInhabitedOfMonad___redArg(x_5, x_6);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_2(x_8, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
x_18 = lean_st_ref_get(x_7, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_array_uget(x_3, x_5);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_24);
x_29 = l_Lean_Name_hash___override(x_27);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_24, x_43);
lean_dec(x_24);
x_45 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_27, x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_dec(x_27);
lean_free_object(x_18);
x_9 = x_25;
x_10 = x_22;
goto block_15;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_dec(x_27);
lean_free_object(x_18);
x_9 = x_25;
x_10 = x_22;
goto block_15;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*5);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_box(x_50);
x_52 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_52, 0, x_51);
x_53 = lean_mk_string_unchecked("cannot import non`-module` ", 27, 27);
lean_inc(x_52);
x_54 = l_Lean_Name_toString(x_27, x_1, x_52);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_56 = lean_mk_string_unchecked(" from `module` ", 15, 15);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_dec(x_2);
x_59 = l_Lean_Name_toString(x_58, x_1, x_52);
x_60 = lean_string_append(x_57, x_59);
lean_dec(x_59);
lean_ctor_set_tag(x_47, 18);
lean_ctor_set(x_47, 0, x_60);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_47);
return x_18;
}
else
{
lean_free_object(x_47);
lean_dec(x_27);
lean_free_object(x_18);
x_9 = x_25;
x_10 = x_22;
goto block_15;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
lean_dec(x_47);
x_62 = lean_ctor_get_uint8(x_61, sizeof(void*)*5);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_box(x_62);
x_64 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_64, 0, x_63);
x_65 = lean_mk_string_unchecked("cannot import non`-module` ", 27, 27);
lean_inc(x_64);
x_66 = l_Lean_Name_toString(x_27, x_1, x_64);
x_67 = lean_string_append(x_65, x_66);
lean_dec(x_66);
x_68 = lean_mk_string_unchecked(" from `module` ", 15, 15);
x_69 = lean_string_append(x_67, x_68);
lean_dec(x_68);
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
lean_dec(x_2);
x_71 = l_Lean_Name_toString(x_70, x_1, x_64);
x_72 = lean_string_append(x_69, x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_73);
return x_18;
}
else
{
lean_dec(x_27);
lean_free_object(x_18);
x_9 = x_25;
x_10 = x_22;
goto block_15;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint64_t x_80; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; lean_object* x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; size_t x_89; size_t x_90; lean_object* x_91; size_t x_92; size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; 
x_74 = lean_ctor_get(x_18, 1);
lean_inc(x_74);
lean_dec(x_18);
x_75 = lean_ctor_get(x_20, 1);
lean_inc(x_75);
lean_dec(x_20);
x_76 = lean_box(0);
x_77 = lean_array_uget(x_3, x_5);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_array_get_size(x_75);
x_80 = l_Lean_Name_hash___override(x_78);
x_81 = lean_unsigned_to_nat(32u);
x_82 = lean_uint64_of_nat(x_81);
x_83 = lean_uint64_shift_right(x_80, x_82);
x_84 = lean_uint64_xor(x_80, x_83);
x_85 = lean_unsigned_to_nat(16u);
x_86 = lean_uint64_of_nat(x_85);
x_87 = lean_uint64_shift_right(x_84, x_86);
x_88 = lean_uint64_xor(x_84, x_87);
x_89 = lean_uint64_to_usize(x_88);
x_90 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_usize_of_nat(x_91);
x_93 = lean_usize_sub(x_90, x_92);
x_94 = lean_usize_land(x_89, x_93);
x_95 = lean_array_uget(x_75, x_94);
lean_dec(x_75);
x_96 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_78, x_95);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_dec(x_78);
x_9 = x_76;
x_10 = x_74;
goto block_15;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f(x_97);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_dec(x_78);
x_9 = x_76;
x_10 = x_74;
goto block_15;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get_uint8(x_99, sizeof(void*)*5);
lean_dec(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_102 = lean_box(x_101);
x_103 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_103, 0, x_102);
x_104 = lean_mk_string_unchecked("cannot import non`-module` ", 27, 27);
lean_inc(x_103);
x_105 = l_Lean_Name_toString(x_78, x_1, x_103);
x_106 = lean_string_append(x_104, x_105);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked(" from `module` ", 15, 15);
x_108 = lean_string_append(x_106, x_107);
lean_dec(x_107);
x_109 = lean_ctor_get(x_2, 0);
lean_inc(x_109);
lean_dec(x_2);
x_110 = l_Lean_Name_toString(x_109, x_1, x_103);
x_111 = lean_string_append(x_108, x_110);
lean_dec(x_110);
if (lean_is_scalar(x_100)) {
 x_112 = lean_alloc_ctor(18, 1, 0);
} else {
 x_112 = x_100;
 lean_ctor_set_tag(x_112, 18);
}
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_74);
return x_113;
}
else
{
lean_dec(x_100);
lean_dec(x_78);
x_9 = x_76;
x_10 = x_74;
goto block_15;
}
}
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_6 = x_9;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_importModulesCore_go_spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_17; 
x_13 = lean_array_uget(x_2, x_3);
x_17 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
if (x_17 == 0)
{
x_14 = x_1;
goto block_16;
}
else
{
x_14 = x_17;
goto block_16;
}
block_16:
{
if (x_14 == 0)
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_13);
x_6 = x_15;
goto block_11;
}
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_250; 
lean_dec(x_6);
x_18 = lean_box(0);
x_47 = lean_array_uget(x_3, x_5);
if (x_1 == 0)
{
uint8_t x_391; 
x_391 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
x_250 = x_391;
goto block_390;
}
else
{
x_250 = x_1;
goto block_390;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_array_push(x_24, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_st_ref_set(x_21, x_26, x_19);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_9 = x_18;
x_10 = x_28;
goto block_15;
}
block_46:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_set(x_7, x_36, x_33);
if (x_1 == 0)
{
lean_object* x_38; 
lean_dec(x_32);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_9 = x_18;
x_10 = x_38;
goto block_15;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f(x_32);
lean_dec(x_32);
if (lean_obj_tag(x_40) == 0)
{
x_9 = x_18;
x_10 = x_39;
goto block_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
lean_inc(x_7);
x_44 = l_Lean_importModulesCore(x_42, x_31, x_43, x_7, x_39);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_9 = x_18;
x_10 = x_45;
goto block_15;
}
else
{
lean_dec(x_7);
return x_44;
}
}
}
}
block_179:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_st_ref_take(x_50, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_52, 1);
x_57 = lean_ctor_get(x_52, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; size_t x_74; size_t x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
x_61 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 1);
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
lean_dec(x_47);
lean_inc(x_62);
x_63 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 1, x_61);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 0, x_63);
x_64 = lean_array_get_size(x_60);
x_65 = l_Lean_Name_hash___override(x_62);
x_66 = lean_unsigned_to_nat(32u);
x_67 = lean_uint64_of_nat(x_66);
x_68 = lean_uint64_shift_right(x_65, x_67);
x_69 = lean_uint64_xor(x_65, x_68);
x_70 = lean_unsigned_to_nat(16u);
x_71 = lean_uint64_of_nat(x_70);
x_72 = lean_uint64_shift_right(x_69, x_71);
x_73 = lean_uint64_xor(x_69, x_72);
x_74 = lean_uint64_to_usize(x_73);
x_75 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_usize_of_nat(x_76);
x_78 = lean_usize_sub(x_75, x_77);
x_79 = lean_usize_land(x_74, x_78);
x_80 = lean_array_uget(x_60, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_62, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_nat_add(x_59, x_76);
lean_dec(x_59);
lean_inc(x_62);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_52);
lean_ctor_set(x_83, 2, x_80);
x_84 = lean_array_uset(x_60, x_79, x_83);
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_shiftl(x_82, x_85);
x_87 = lean_unsigned_to_nat(3u);
x_88 = lean_nat_div(x_86, x_87);
lean_dec(x_86);
x_89 = lean_array_get_size(x_84);
x_90 = lean_nat_dec_le(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_84);
lean_ctor_set(x_54, 1, x_91);
lean_ctor_set(x_54, 0, x_82);
x_19 = x_56;
x_20 = x_53;
x_21 = x_50;
x_22 = x_62;
x_23 = x_54;
goto block_29;
}
else
{
lean_ctor_set(x_54, 1, x_84);
lean_ctor_set(x_54, 0, x_82);
x_19 = x_56;
x_20 = x_53;
x_21 = x_50;
x_22 = x_62;
x_23 = x_54;
goto block_29;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_box(0);
x_93 = lean_array_uset(x_60, x_79, x_92);
lean_inc(x_62);
x_94 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_62, x_52, x_80);
x_95 = lean_array_uset(x_93, x_79, x_94);
lean_ctor_set(x_54, 1, x_95);
x_19 = x_56;
x_20 = x_53;
x_21 = x_50;
x_22 = x_62;
x_23 = x_54;
goto block_29;
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint64_t x_102; lean_object* x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; lean_object* x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; size_t x_111; size_t x_112; lean_object* x_113; size_t x_114; size_t x_115; size_t x_116; lean_object* x_117; uint8_t x_118; 
x_96 = lean_ctor_get(x_54, 0);
x_97 = lean_ctor_get(x_54, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_54);
x_98 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 1);
x_99 = lean_ctor_get(x_47, 0);
lean_inc(x_99);
lean_dec(x_47);
lean_inc(x_99);
x_100 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_100, sizeof(void*)*1 + 1, x_98);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 0, x_100);
x_101 = lean_array_get_size(x_97);
x_102 = l_Lean_Name_hash___override(x_99);
x_103 = lean_unsigned_to_nat(32u);
x_104 = lean_uint64_of_nat(x_103);
x_105 = lean_uint64_shift_right(x_102, x_104);
x_106 = lean_uint64_xor(x_102, x_105);
x_107 = lean_unsigned_to_nat(16u);
x_108 = lean_uint64_of_nat(x_107);
x_109 = lean_uint64_shift_right(x_106, x_108);
x_110 = lean_uint64_xor(x_106, x_109);
x_111 = lean_uint64_to_usize(x_110);
x_112 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_usize_of_nat(x_113);
x_115 = lean_usize_sub(x_112, x_114);
x_116 = lean_usize_land(x_111, x_115);
x_117 = lean_array_uget(x_97, x_116);
x_118 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_99, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_119 = lean_nat_add(x_96, x_113);
lean_dec(x_96);
lean_inc(x_99);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_99);
lean_ctor_set(x_120, 1, x_52);
lean_ctor_set(x_120, 2, x_117);
x_121 = lean_array_uset(x_97, x_116, x_120);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_nat_shiftl(x_119, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = lean_array_get_size(x_121);
x_127 = lean_nat_dec_le(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_121);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_128);
x_19 = x_56;
x_20 = x_53;
x_21 = x_50;
x_22 = x_99;
x_23 = x_129;
goto block_29;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_119);
lean_ctor_set(x_130, 1, x_121);
x_19 = x_56;
x_20 = x_53;
x_21 = x_50;
x_22 = x_99;
x_23 = x_130;
goto block_29;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_box(0);
x_132 = lean_array_uset(x_97, x_116, x_131);
lean_inc(x_99);
x_133 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_99, x_52, x_117);
x_134 = lean_array_uset(x_132, x_116, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_96);
lean_ctor_set(x_135, 1, x_134);
x_19 = x_56;
x_20 = x_53;
x_21 = x_50;
x_22 = x_99;
x_23 = x_135;
goto block_29;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint64_t x_145; lean_object* x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; lean_object* x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; size_t x_154; size_t x_155; lean_object* x_156; size_t x_157; size_t x_158; size_t x_159; lean_object* x_160; uint8_t x_161; 
x_136 = lean_ctor_get(x_52, 1);
lean_inc(x_136);
lean_dec(x_52);
x_137 = lean_ctor_get(x_54, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_54, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_139 = x_54;
} else {
 lean_dec_ref(x_54);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 1);
x_141 = lean_ctor_get(x_47, 0);
lean_inc(x_141);
lean_dec(x_47);
lean_inc(x_141);
x_142 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_142, sizeof(void*)*1 + 1, x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_49);
x_144 = lean_array_get_size(x_138);
x_145 = l_Lean_Name_hash___override(x_141);
x_146 = lean_unsigned_to_nat(32u);
x_147 = lean_uint64_of_nat(x_146);
x_148 = lean_uint64_shift_right(x_145, x_147);
x_149 = lean_uint64_xor(x_145, x_148);
x_150 = lean_unsigned_to_nat(16u);
x_151 = lean_uint64_of_nat(x_150);
x_152 = lean_uint64_shift_right(x_149, x_151);
x_153 = lean_uint64_xor(x_149, x_152);
x_154 = lean_uint64_to_usize(x_153);
x_155 = lean_usize_of_nat(x_144);
lean_dec(x_144);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_usize_of_nat(x_156);
x_158 = lean_usize_sub(x_155, x_157);
x_159 = lean_usize_land(x_154, x_158);
x_160 = lean_array_uget(x_138, x_159);
x_161 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_141, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_162 = lean_nat_add(x_137, x_156);
lean_dec(x_137);
lean_inc(x_141);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_141);
lean_ctor_set(x_163, 1, x_143);
lean_ctor_set(x_163, 2, x_160);
x_164 = lean_array_uset(x_138, x_159, x_163);
x_165 = lean_unsigned_to_nat(2u);
x_166 = lean_nat_shiftl(x_162, x_165);
x_167 = lean_unsigned_to_nat(3u);
x_168 = lean_nat_div(x_166, x_167);
lean_dec(x_166);
x_169 = lean_array_get_size(x_164);
x_170 = lean_nat_dec_le(x_168, x_169);
lean_dec(x_169);
lean_dec(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_164);
if (lean_is_scalar(x_139)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_139;
}
lean_ctor_set(x_172, 0, x_162);
lean_ctor_set(x_172, 1, x_171);
x_19 = x_136;
x_20 = x_53;
x_21 = x_50;
x_22 = x_141;
x_23 = x_172;
goto block_29;
}
else
{
lean_object* x_173; 
if (lean_is_scalar(x_139)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_139;
}
lean_ctor_set(x_173, 0, x_162);
lean_ctor_set(x_173, 1, x_164);
x_19 = x_136;
x_20 = x_53;
x_21 = x_50;
x_22 = x_141;
x_23 = x_173;
goto block_29;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_box(0);
x_175 = lean_array_uset(x_138, x_159, x_174);
lean_inc(x_141);
x_176 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_141, x_143, x_160);
x_177 = lean_array_uset(x_175, x_159, x_176);
if (lean_is_scalar(x_139)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_139;
}
lean_ctor_set(x_178, 0, x_137);
lean_ctor_set(x_178, 1, x_177);
x_19 = x_136;
x_20 = x_53;
x_21 = x_50;
x_22 = x_141;
x_23 = x_178;
goto block_29;
}
}
}
block_191:
{
if (x_186 == 0)
{
lean_dec(x_180);
x_48 = x_182;
x_49 = x_184;
x_50 = x_183;
x_51 = x_185;
goto block_179;
}
else
{
size_t x_187; size_t x_188; lean_object* x_189; 
x_187 = lean_array_size(x_180);
x_188 = lean_usize_of_nat(x_181);
lean_inc(x_47);
x_189 = l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1(x_186, x_47, x_180, x_187, x_188, x_18, x_183, x_185);
lean_dec(x_180);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_48 = x_182;
x_49 = x_184;
x_50 = x_183;
x_51 = x_190;
goto block_179;
}
else
{
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_47);
lean_dec(x_7);
return x_189;
}
}
}
block_206:
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_box(0);
lean_inc(x_197);
x_201 = l_Lean_importModulesCore(x_192, x_199, x_200, x_197, x_196);
if (lean_obj_tag(x_201) == 0)
{
uint8_t x_202; 
x_202 = lean_ctor_get_uint8(x_195, sizeof(void*)*5);
lean_dec(x_195);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_180 = x_192;
x_181 = x_194;
x_182 = x_193;
x_183 = x_197;
x_184 = x_198;
x_185 = x_203;
x_186 = x_202;
goto block_191;
}
else
{
if (x_1 == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_180 = x_192;
x_181 = x_194;
x_182 = x_193;
x_183 = x_197;
x_184 = x_198;
x_185 = x_204;
x_186 = x_202;
goto block_191;
}
else
{
lean_object* x_205; 
lean_dec(x_192);
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
lean_dec(x_201);
x_48 = x_193;
x_49 = x_198;
x_50 = x_197;
x_51 = x_205;
goto block_179;
}
}
}
else
{
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_192);
lean_dec(x_47);
lean_dec(x_7);
return x_201;
}
}
block_216:
{
if (x_1 == 0)
{
uint8_t x_215; 
x_215 = lean_ctor_get_uint8(x_210, sizeof(void*)*5);
if (x_215 == 0)
{
x_192 = x_214;
x_193 = x_208;
x_194 = x_207;
x_195 = x_210;
x_196 = x_212;
x_197 = x_211;
x_198 = x_213;
x_199 = x_209;
goto block_206;
}
else
{
x_192 = x_214;
x_193 = x_208;
x_194 = x_207;
x_195 = x_210;
x_196 = x_212;
x_197 = x_211;
x_198 = x_213;
x_199 = x_1;
goto block_206;
}
}
else
{
x_192 = x_214;
x_193 = x_208;
x_194 = x_207;
x_195 = x_210;
x_196 = x_212;
x_197 = x_211;
x_198 = x_213;
x_199 = x_1;
goto block_206;
}
}
block_249:
{
lean_object* x_221; 
x_221 = lean_read_module_data_parts(x_218, x_220);
lean_dec(x_218);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_unsigned_to_nat(0u);
x_225 = lean_array_get_size(x_222);
x_226 = lean_nat_dec_lt(x_224, x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_222);
lean_dec(x_47);
x_227 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_228 = lean_mk_string_unchecked("Lean.importModulesCore.go", 25, 25);
x_229 = lean_unsigned_to_nat(1845u);
x_230 = lean_unsigned_to_nat(41u);
x_231 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_232 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_227, x_228, x_229, x_230, x_231);
lean_dec(x_231);
lean_dec(x_228);
lean_dec(x_227);
x_233 = l_panic___at___Lean_importModulesCore_go_spec__0(x_232, x_219, x_223);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_9 = x_18;
x_10 = x_234;
goto block_15;
}
else
{
lean_dec(x_7);
return x_233;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_235 = lean_array_fget(x_222, x_224);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_array_get_size(x_237);
x_239 = lean_mk_empty_array_with_capacity(x_224);
x_240 = lean_nat_dec_lt(x_224, x_238);
if (x_240 == 0)
{
lean_dec(x_238);
lean_dec(x_237);
x_207 = x_224;
x_208 = x_217;
x_209 = x_226;
x_210 = x_236;
x_211 = x_219;
x_212 = x_223;
x_213 = x_222;
x_214 = x_239;
goto block_216;
}
else
{
uint8_t x_241; 
x_241 = lean_nat_dec_le(x_238, x_238);
if (x_241 == 0)
{
lean_dec(x_238);
lean_dec(x_237);
x_207 = x_224;
x_208 = x_217;
x_209 = x_226;
x_210 = x_236;
x_211 = x_219;
x_212 = x_223;
x_213 = x_222;
x_214 = x_239;
goto block_216;
}
else
{
size_t x_242; size_t x_243; lean_object* x_244; 
x_242 = lean_usize_of_nat(x_224);
x_243 = lean_usize_of_nat(x_238);
lean_dec(x_238);
x_244 = l_Array_foldlMUnsafe_fold___at___Lean_importModulesCore_go_spec__2(x_217, x_237, x_242, x_243, x_239);
lean_dec(x_237);
x_207 = x_224;
x_208 = x_217;
x_209 = x_226;
x_210 = x_236;
x_211 = x_219;
x_212 = x_223;
x_213 = x_222;
x_214 = x_244;
goto block_216;
}
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_219);
lean_dec(x_47);
lean_dec(x_7);
x_245 = !lean_is_exclusive(x_221);
if (x_245 == 0)
{
return x_221;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_221, 0);
x_247 = lean_ctor_get(x_221, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_221);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
block_390:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint64_t x_258; lean_object* x_259; uint64_t x_260; uint64_t x_261; uint64_t x_262; lean_object* x_263; uint64_t x_264; uint64_t x_265; uint64_t x_266; size_t x_267; size_t x_268; lean_object* x_269; size_t x_270; size_t x_271; size_t x_272; lean_object* x_273; lean_object* x_274; 
x_251 = lean_st_ref_get(x_7, x_8);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_47, 0);
lean_inc(x_256);
x_257 = lean_array_get_size(x_255);
x_258 = l_Lean_Name_hash___override(x_256);
x_259 = lean_unsigned_to_nat(32u);
x_260 = lean_uint64_of_nat(x_259);
x_261 = lean_uint64_shift_right(x_258, x_260);
x_262 = lean_uint64_xor(x_258, x_261);
x_263 = lean_unsigned_to_nat(16u);
x_264 = lean_uint64_of_nat(x_263);
x_265 = lean_uint64_shift_right(x_262, x_264);
x_266 = lean_uint64_xor(x_262, x_265);
x_267 = lean_uint64_to_usize(x_266);
x_268 = lean_usize_of_nat(x_257);
lean_dec(x_257);
x_269 = lean_unsigned_to_nat(1u);
x_270 = lean_usize_of_nat(x_269);
x_271 = lean_usize_sub(x_268, x_270);
x_272 = lean_usize_land(x_267, x_271);
x_273 = lean_array_uget(x_255, x_272);
lean_dec(x_255);
x_274 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_256, x_273);
lean_dec(x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; 
x_275 = l_Lean_NameMap_find_x3f(lean_box(0), x_2, x_256);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
x_276 = l___private_Lean_Environment_0__Lean_findOLeanParts(x_256, x_254);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
lean_inc(x_7);
x_217 = x_250;
x_218 = x_277;
x_219 = x_7;
x_220 = x_278;
goto block_249;
}
else
{
uint8_t x_279; 
lean_dec(x_47);
lean_dec(x_7);
x_279 = !lean_is_exclusive(x_276);
if (x_279 == 0)
{
return x_276;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_276, 0);
x_281 = lean_ctor_get(x_276, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_276);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_275, 0);
lean_inc(x_283);
lean_dec(x_275);
x_284 = l_Lean_ModuleArtifacts_oleanParts(x_283);
x_285 = l_Array_isEmpty___redArg(x_284);
if (x_285 == 0)
{
lean_dec(x_256);
lean_inc(x_7);
x_217 = x_250;
x_218 = x_284;
x_219 = x_7;
x_220 = x_254;
goto block_249;
}
else
{
lean_object* x_286; 
lean_dec(x_284);
x_286 = l___private_Lean_Environment_0__Lean_findOLeanParts(x_256, x_254);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_7);
x_217 = x_250;
x_218 = x_287;
x_219 = x_7;
x_220 = x_288;
goto block_249;
}
else
{
uint8_t x_289; 
lean_dec(x_47);
lean_dec(x_7);
x_289 = !lean_is_exclusive(x_286);
if (x_289 == 0)
{
return x_286;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_286, 0);
x_291 = lean_ctor_get(x_286, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_286);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
}
}
else
{
lean_dec(x_47);
if (x_250 == 0)
{
lean_dec(x_274);
lean_dec(x_256);
x_9 = x_18;
x_10 = x_254;
goto block_15;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = lean_ctor_get(x_274, 0);
lean_inc(x_293);
lean_dec(x_274);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get_uint8(x_294, sizeof(void*)*1);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_st_ref_take(x_7, x_254);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = !lean_is_exclusive(x_296);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_296, 1);
x_301 = lean_ctor_get(x_296, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_298);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; size_t x_310; size_t x_311; size_t x_312; lean_object* x_313; uint8_t x_314; 
x_303 = lean_ctor_get(x_298, 0);
x_304 = lean_ctor_get(x_298, 1);
x_305 = lean_ctor_get(x_294, 0);
lean_inc(x_305);
x_306 = lean_ctor_get_uint8(x_294, sizeof(void*)*1 + 1);
lean_dec(x_294);
x_307 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set_uint8(x_307, sizeof(void*)*1, x_250);
lean_ctor_set_uint8(x_307, sizeof(void*)*1 + 1, x_306);
x_308 = lean_ctor_get(x_293, 1);
lean_inc(x_308);
lean_ctor_set(x_296, 1, x_308);
lean_ctor_set(x_296, 0, x_307);
x_309 = lean_array_get_size(x_304);
x_310 = lean_usize_of_nat(x_309);
lean_dec(x_309);
x_311 = lean_usize_sub(x_310, x_270);
x_312 = lean_usize_land(x_267, x_311);
x_313 = lean_array_uget(x_304, x_312);
x_314 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_256, x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_315 = lean_nat_add(x_303, x_269);
lean_dec(x_303);
x_316 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_316, 0, x_256);
lean_ctor_set(x_316, 1, x_296);
lean_ctor_set(x_316, 2, x_313);
x_317 = lean_array_uset(x_304, x_312, x_316);
x_318 = lean_unsigned_to_nat(2u);
x_319 = lean_nat_shiftl(x_315, x_318);
x_320 = lean_unsigned_to_nat(3u);
x_321 = lean_nat_div(x_319, x_320);
lean_dec(x_319);
x_322 = lean_array_get_size(x_317);
x_323 = lean_nat_dec_le(x_321, x_322);
lean_dec(x_322);
lean_dec(x_321);
if (x_323 == 0)
{
lean_object* x_324; 
x_324 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_317);
lean_ctor_set(x_298, 1, x_324);
lean_ctor_set(x_298, 0, x_315);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_300;
x_34 = x_298;
goto block_46;
}
else
{
lean_ctor_set(x_298, 1, x_317);
lean_ctor_set(x_298, 0, x_315);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_300;
x_34 = x_298;
goto block_46;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_box(0);
x_326 = lean_array_uset(x_304, x_312, x_325);
x_327 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_256, x_296, x_313);
x_328 = lean_array_uset(x_326, x_312, x_327);
lean_ctor_set(x_298, 1, x_328);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_300;
x_34 = x_298;
goto block_46;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; size_t x_336; size_t x_337; size_t x_338; lean_object* x_339; uint8_t x_340; 
x_329 = lean_ctor_get(x_298, 0);
x_330 = lean_ctor_get(x_298, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_298);
x_331 = lean_ctor_get(x_294, 0);
lean_inc(x_331);
x_332 = lean_ctor_get_uint8(x_294, sizeof(void*)*1 + 1);
lean_dec(x_294);
x_333 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*1, x_250);
lean_ctor_set_uint8(x_333, sizeof(void*)*1 + 1, x_332);
x_334 = lean_ctor_get(x_293, 1);
lean_inc(x_334);
lean_ctor_set(x_296, 1, x_334);
lean_ctor_set(x_296, 0, x_333);
x_335 = lean_array_get_size(x_330);
x_336 = lean_usize_of_nat(x_335);
lean_dec(x_335);
x_337 = lean_usize_sub(x_336, x_270);
x_338 = lean_usize_land(x_267, x_337);
x_339 = lean_array_uget(x_330, x_338);
x_340 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_256, x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_341 = lean_nat_add(x_329, x_269);
lean_dec(x_329);
x_342 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_342, 0, x_256);
lean_ctor_set(x_342, 1, x_296);
lean_ctor_set(x_342, 2, x_339);
x_343 = lean_array_uset(x_330, x_338, x_342);
x_344 = lean_unsigned_to_nat(2u);
x_345 = lean_nat_shiftl(x_341, x_344);
x_346 = lean_unsigned_to_nat(3u);
x_347 = lean_nat_div(x_345, x_346);
lean_dec(x_345);
x_348 = lean_array_get_size(x_343);
x_349 = lean_nat_dec_le(x_347, x_348);
lean_dec(x_348);
lean_dec(x_347);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_343);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_341);
lean_ctor_set(x_351, 1, x_350);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_300;
x_34 = x_351;
goto block_46;
}
else
{
lean_object* x_352; 
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_341);
lean_ctor_set(x_352, 1, x_343);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_300;
x_34 = x_352;
goto block_46;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_box(0);
x_354 = lean_array_uset(x_330, x_338, x_353);
x_355 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_256, x_296, x_339);
x_356 = lean_array_uset(x_354, x_338, x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_329);
lean_ctor_set(x_357, 1, x_356);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_300;
x_34 = x_357;
goto block_46;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; size_t x_368; size_t x_369; size_t x_370; lean_object* x_371; uint8_t x_372; 
x_358 = lean_ctor_get(x_296, 1);
lean_inc(x_358);
lean_dec(x_296);
x_359 = lean_ctor_get(x_298, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_298, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_361 = x_298;
} else {
 lean_dec_ref(x_298);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_294, 0);
lean_inc(x_362);
x_363 = lean_ctor_get_uint8(x_294, sizeof(void*)*1 + 1);
lean_dec(x_294);
x_364 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set_uint8(x_364, sizeof(void*)*1, x_250);
lean_ctor_set_uint8(x_364, sizeof(void*)*1 + 1, x_363);
x_365 = lean_ctor_get(x_293, 1);
lean_inc(x_365);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_array_get_size(x_360);
x_368 = lean_usize_of_nat(x_367);
lean_dec(x_367);
x_369 = lean_usize_sub(x_368, x_270);
x_370 = lean_usize_land(x_267, x_369);
x_371 = lean_array_uget(x_360, x_370);
x_372 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_256, x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_373 = lean_nat_add(x_359, x_269);
lean_dec(x_359);
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_256);
lean_ctor_set(x_374, 1, x_366);
lean_ctor_set(x_374, 2, x_371);
x_375 = lean_array_uset(x_360, x_370, x_374);
x_376 = lean_unsigned_to_nat(2u);
x_377 = lean_nat_shiftl(x_373, x_376);
x_378 = lean_unsigned_to_nat(3u);
x_379 = lean_nat_div(x_377, x_378);
lean_dec(x_377);
x_380 = lean_array_get_size(x_375);
x_381 = lean_nat_dec_le(x_379, x_380);
lean_dec(x_380);
lean_dec(x_379);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_375);
if (lean_is_scalar(x_361)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_361;
}
lean_ctor_set(x_383, 0, x_373);
lean_ctor_set(x_383, 1, x_382);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_358;
x_34 = x_383;
goto block_46;
}
else
{
lean_object* x_384; 
if (lean_is_scalar(x_361)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_361;
}
lean_ctor_set(x_384, 0, x_373);
lean_ctor_set(x_384, 1, x_375);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_358;
x_34 = x_384;
goto block_46;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_385 = lean_box(0);
x_386 = lean_array_uset(x_360, x_370, x_385);
x_387 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_256, x_366, x_371);
x_388 = lean_array_uset(x_386, x_370, x_387);
if (lean_is_scalar(x_361)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_361;
}
lean_ctor_set(x_389, 0, x_359);
lean_ctor_set(x_389, 1, x_388);
x_30 = x_297;
x_31 = x_250;
x_32 = x_293;
x_33 = x_358;
x_34 = x_389;
goto block_46;
}
}
}
else
{
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_256);
x_9 = x_18;
x_10 = x_254;
goto block_15;
}
}
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_6 = x_9;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; uint8_t x_186; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_250; 
lean_dec(x_6);
x_18 = lean_box(0);
x_47 = lean_array_uget(x_3, x_5);
if (x_1 == 0)
{
uint8_t x_391; 
x_391 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
x_250 = x_391;
goto block_390;
}
else
{
x_250 = x_1;
goto block_390;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_push(x_24, x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_st_ref_set(x_20, x_26, x_19);
lean_dec(x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_9 = x_18;
x_10 = x_28;
goto block_15;
}
block_46:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_set(x_7, x_36, x_30);
if (x_1 == 0)
{
lean_object* x_38; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_9 = x_18;
x_10 = x_38;
goto block_15;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f(x_31);
lean_dec(x_31);
if (lean_obj_tag(x_40) == 0)
{
x_9 = x_18;
x_10 = x_39;
goto block_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
lean_inc(x_7);
x_44 = l_Lean_importModulesCore(x_42, x_32, x_43, x_7, x_39);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_9 = x_18;
x_10 = x_45;
goto block_15;
}
else
{
lean_dec(x_7);
return x_44;
}
}
}
}
block_179:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_st_ref_take(x_50, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_52, 1);
x_57 = lean_ctor_get(x_52, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; size_t x_74; size_t x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
x_61 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 1);
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
lean_dec(x_47);
lean_inc(x_62);
x_63 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_49);
lean_ctor_set_uint8(x_63, sizeof(void*)*1 + 1, x_61);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 0, x_63);
x_64 = lean_array_get_size(x_60);
x_65 = l_Lean_Name_hash___override(x_62);
x_66 = lean_unsigned_to_nat(32u);
x_67 = lean_uint64_of_nat(x_66);
x_68 = lean_uint64_shift_right(x_65, x_67);
x_69 = lean_uint64_xor(x_65, x_68);
x_70 = lean_unsigned_to_nat(16u);
x_71 = lean_uint64_of_nat(x_70);
x_72 = lean_uint64_shift_right(x_69, x_71);
x_73 = lean_uint64_xor(x_69, x_72);
x_74 = lean_uint64_to_usize(x_73);
x_75 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_usize_of_nat(x_76);
x_78 = lean_usize_sub(x_75, x_77);
x_79 = lean_usize_land(x_74, x_78);
x_80 = lean_array_uget(x_60, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_62, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_nat_add(x_59, x_76);
lean_dec(x_59);
lean_inc(x_62);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_52);
lean_ctor_set(x_83, 2, x_80);
x_84 = lean_array_uset(x_60, x_79, x_83);
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_shiftl(x_82, x_85);
x_87 = lean_unsigned_to_nat(3u);
x_88 = lean_nat_div(x_86, x_87);
lean_dec(x_86);
x_89 = lean_array_get_size(x_84);
x_90 = lean_nat_dec_le(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_84);
lean_ctor_set(x_54, 1, x_91);
lean_ctor_set(x_54, 0, x_82);
x_19 = x_56;
x_20 = x_50;
x_21 = x_62;
x_22 = x_53;
x_23 = x_54;
goto block_29;
}
else
{
lean_ctor_set(x_54, 1, x_84);
lean_ctor_set(x_54, 0, x_82);
x_19 = x_56;
x_20 = x_50;
x_21 = x_62;
x_22 = x_53;
x_23 = x_54;
goto block_29;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_box(0);
x_93 = lean_array_uset(x_60, x_79, x_92);
lean_inc(x_62);
x_94 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_62, x_52, x_80);
x_95 = lean_array_uset(x_93, x_79, x_94);
lean_ctor_set(x_54, 1, x_95);
x_19 = x_56;
x_20 = x_50;
x_21 = x_62;
x_22 = x_53;
x_23 = x_54;
goto block_29;
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint64_t x_102; lean_object* x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; lean_object* x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; size_t x_111; size_t x_112; lean_object* x_113; size_t x_114; size_t x_115; size_t x_116; lean_object* x_117; uint8_t x_118; 
x_96 = lean_ctor_get(x_54, 0);
x_97 = lean_ctor_get(x_54, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_54);
x_98 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 1);
x_99 = lean_ctor_get(x_47, 0);
lean_inc(x_99);
lean_dec(x_47);
lean_inc(x_99);
x_100 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_49);
lean_ctor_set_uint8(x_100, sizeof(void*)*1 + 1, x_98);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 0, x_100);
x_101 = lean_array_get_size(x_97);
x_102 = l_Lean_Name_hash___override(x_99);
x_103 = lean_unsigned_to_nat(32u);
x_104 = lean_uint64_of_nat(x_103);
x_105 = lean_uint64_shift_right(x_102, x_104);
x_106 = lean_uint64_xor(x_102, x_105);
x_107 = lean_unsigned_to_nat(16u);
x_108 = lean_uint64_of_nat(x_107);
x_109 = lean_uint64_shift_right(x_106, x_108);
x_110 = lean_uint64_xor(x_106, x_109);
x_111 = lean_uint64_to_usize(x_110);
x_112 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_usize_of_nat(x_113);
x_115 = lean_usize_sub(x_112, x_114);
x_116 = lean_usize_land(x_111, x_115);
x_117 = lean_array_uget(x_97, x_116);
x_118 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_99, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_119 = lean_nat_add(x_96, x_113);
lean_dec(x_96);
lean_inc(x_99);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_99);
lean_ctor_set(x_120, 1, x_52);
lean_ctor_set(x_120, 2, x_117);
x_121 = lean_array_uset(x_97, x_116, x_120);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_nat_shiftl(x_119, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = lean_array_get_size(x_121);
x_127 = lean_nat_dec_le(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_121);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_128);
x_19 = x_56;
x_20 = x_50;
x_21 = x_99;
x_22 = x_53;
x_23 = x_129;
goto block_29;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_119);
lean_ctor_set(x_130, 1, x_121);
x_19 = x_56;
x_20 = x_50;
x_21 = x_99;
x_22 = x_53;
x_23 = x_130;
goto block_29;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_box(0);
x_132 = lean_array_uset(x_97, x_116, x_131);
lean_inc(x_99);
x_133 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_99, x_52, x_117);
x_134 = lean_array_uset(x_132, x_116, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_96);
lean_ctor_set(x_135, 1, x_134);
x_19 = x_56;
x_20 = x_50;
x_21 = x_99;
x_22 = x_53;
x_23 = x_135;
goto block_29;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint64_t x_145; lean_object* x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; lean_object* x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; size_t x_154; size_t x_155; lean_object* x_156; size_t x_157; size_t x_158; size_t x_159; lean_object* x_160; uint8_t x_161; 
x_136 = lean_ctor_get(x_52, 1);
lean_inc(x_136);
lean_dec(x_52);
x_137 = lean_ctor_get(x_54, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_54, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_139 = x_54;
} else {
 lean_dec_ref(x_54);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 1);
x_141 = lean_ctor_get(x_47, 0);
lean_inc(x_141);
lean_dec(x_47);
lean_inc(x_141);
x_142 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_49);
lean_ctor_set_uint8(x_142, sizeof(void*)*1 + 1, x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_48);
x_144 = lean_array_get_size(x_138);
x_145 = l_Lean_Name_hash___override(x_141);
x_146 = lean_unsigned_to_nat(32u);
x_147 = lean_uint64_of_nat(x_146);
x_148 = lean_uint64_shift_right(x_145, x_147);
x_149 = lean_uint64_xor(x_145, x_148);
x_150 = lean_unsigned_to_nat(16u);
x_151 = lean_uint64_of_nat(x_150);
x_152 = lean_uint64_shift_right(x_149, x_151);
x_153 = lean_uint64_xor(x_149, x_152);
x_154 = lean_uint64_to_usize(x_153);
x_155 = lean_usize_of_nat(x_144);
lean_dec(x_144);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_usize_of_nat(x_156);
x_158 = lean_usize_sub(x_155, x_157);
x_159 = lean_usize_land(x_154, x_158);
x_160 = lean_array_uget(x_138, x_159);
x_161 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_141, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_162 = lean_nat_add(x_137, x_156);
lean_dec(x_137);
lean_inc(x_141);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_141);
lean_ctor_set(x_163, 1, x_143);
lean_ctor_set(x_163, 2, x_160);
x_164 = lean_array_uset(x_138, x_159, x_163);
x_165 = lean_unsigned_to_nat(2u);
x_166 = lean_nat_shiftl(x_162, x_165);
x_167 = lean_unsigned_to_nat(3u);
x_168 = lean_nat_div(x_166, x_167);
lean_dec(x_166);
x_169 = lean_array_get_size(x_164);
x_170 = lean_nat_dec_le(x_168, x_169);
lean_dec(x_169);
lean_dec(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_164);
if (lean_is_scalar(x_139)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_139;
}
lean_ctor_set(x_172, 0, x_162);
lean_ctor_set(x_172, 1, x_171);
x_19 = x_136;
x_20 = x_50;
x_21 = x_141;
x_22 = x_53;
x_23 = x_172;
goto block_29;
}
else
{
lean_object* x_173; 
if (lean_is_scalar(x_139)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_139;
}
lean_ctor_set(x_173, 0, x_162);
lean_ctor_set(x_173, 1, x_164);
x_19 = x_136;
x_20 = x_50;
x_21 = x_141;
x_22 = x_53;
x_23 = x_173;
goto block_29;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_box(0);
x_175 = lean_array_uset(x_138, x_159, x_174);
lean_inc(x_141);
x_176 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_141, x_143, x_160);
x_177 = lean_array_uset(x_175, x_159, x_176);
if (lean_is_scalar(x_139)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_139;
}
lean_ctor_set(x_178, 0, x_137);
lean_ctor_set(x_178, 1, x_177);
x_19 = x_136;
x_20 = x_50;
x_21 = x_141;
x_22 = x_53;
x_23 = x_178;
goto block_29;
}
}
}
block_191:
{
if (x_186 == 0)
{
lean_dec(x_182);
x_48 = x_180;
x_49 = x_184;
x_50 = x_181;
x_51 = x_185;
goto block_179;
}
else
{
size_t x_187; size_t x_188; lean_object* x_189; 
x_187 = lean_array_size(x_182);
x_188 = lean_usize_of_nat(x_183);
lean_inc(x_47);
x_189 = l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1(x_186, x_47, x_182, x_187, x_188, x_18, x_181, x_185);
lean_dec(x_182);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_48 = x_180;
x_49 = x_184;
x_50 = x_181;
x_51 = x_190;
goto block_179;
}
else
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_47);
lean_dec(x_7);
return x_189;
}
}
}
block_206:
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_box(0);
lean_inc(x_193);
x_201 = l_Lean_importModulesCore(x_194, x_199, x_200, x_193, x_198);
if (lean_obj_tag(x_201) == 0)
{
uint8_t x_202; 
x_202 = lean_ctor_get_uint8(x_195, sizeof(void*)*5);
lean_dec(x_195);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_180 = x_192;
x_181 = x_193;
x_182 = x_194;
x_183 = x_197;
x_184 = x_196;
x_185 = x_203;
x_186 = x_202;
goto block_191;
}
else
{
if (x_1 == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_180 = x_192;
x_181 = x_193;
x_182 = x_194;
x_183 = x_197;
x_184 = x_196;
x_185 = x_204;
x_186 = x_202;
goto block_191;
}
else
{
lean_object* x_205; 
lean_dec(x_194);
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
lean_dec(x_201);
x_48 = x_192;
x_49 = x_196;
x_50 = x_193;
x_51 = x_205;
goto block_179;
}
}
}
else
{
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_47);
lean_dec(x_7);
return x_201;
}
}
block_216:
{
if (x_1 == 0)
{
uint8_t x_215; 
x_215 = lean_ctor_get_uint8(x_211, sizeof(void*)*5);
if (x_215 == 0)
{
x_192 = x_207;
x_193 = x_208;
x_194 = x_214;
x_195 = x_211;
x_196 = x_210;
x_197 = x_209;
x_198 = x_213;
x_199 = x_212;
goto block_206;
}
else
{
x_192 = x_207;
x_193 = x_208;
x_194 = x_214;
x_195 = x_211;
x_196 = x_210;
x_197 = x_209;
x_198 = x_213;
x_199 = x_1;
goto block_206;
}
}
else
{
x_192 = x_207;
x_193 = x_208;
x_194 = x_214;
x_195 = x_211;
x_196 = x_210;
x_197 = x_209;
x_198 = x_213;
x_199 = x_1;
goto block_206;
}
}
block_249:
{
lean_object* x_221; 
x_221 = lean_read_module_data_parts(x_218, x_220);
lean_dec(x_218);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_unsigned_to_nat(0u);
x_225 = lean_array_get_size(x_222);
x_226 = lean_nat_dec_lt(x_224, x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_222);
lean_dec(x_47);
x_227 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_228 = lean_mk_string_unchecked("Lean.importModulesCore.go", 25, 25);
x_229 = lean_unsigned_to_nat(1845u);
x_230 = lean_unsigned_to_nat(41u);
x_231 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_232 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_227, x_228, x_229, x_230, x_231);
lean_dec(x_231);
lean_dec(x_228);
lean_dec(x_227);
x_233 = l_panic___at___Lean_importModulesCore_go_spec__0(x_232, x_219, x_223);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_9 = x_18;
x_10 = x_234;
goto block_15;
}
else
{
lean_dec(x_7);
return x_233;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_235 = lean_array_fget(x_222, x_224);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_array_get_size(x_237);
x_239 = lean_mk_empty_array_with_capacity(x_224);
x_240 = lean_nat_dec_lt(x_224, x_238);
if (x_240 == 0)
{
lean_dec(x_238);
lean_dec(x_237);
x_207 = x_222;
x_208 = x_219;
x_209 = x_224;
x_210 = x_217;
x_211 = x_236;
x_212 = x_226;
x_213 = x_223;
x_214 = x_239;
goto block_216;
}
else
{
uint8_t x_241; 
x_241 = lean_nat_dec_le(x_238, x_238);
if (x_241 == 0)
{
lean_dec(x_238);
lean_dec(x_237);
x_207 = x_222;
x_208 = x_219;
x_209 = x_224;
x_210 = x_217;
x_211 = x_236;
x_212 = x_226;
x_213 = x_223;
x_214 = x_239;
goto block_216;
}
else
{
size_t x_242; size_t x_243; lean_object* x_244; 
x_242 = lean_usize_of_nat(x_224);
x_243 = lean_usize_of_nat(x_238);
lean_dec(x_238);
x_244 = l_Array_foldlMUnsafe_fold___at___Lean_importModulesCore_go_spec__2(x_217, x_237, x_242, x_243, x_239);
lean_dec(x_237);
x_207 = x_222;
x_208 = x_219;
x_209 = x_224;
x_210 = x_217;
x_211 = x_236;
x_212 = x_226;
x_213 = x_223;
x_214 = x_244;
goto block_216;
}
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_219);
lean_dec(x_47);
lean_dec(x_7);
x_245 = !lean_is_exclusive(x_221);
if (x_245 == 0)
{
return x_221;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_221, 0);
x_247 = lean_ctor_get(x_221, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_221);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
block_390:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint64_t x_258; lean_object* x_259; uint64_t x_260; uint64_t x_261; uint64_t x_262; lean_object* x_263; uint64_t x_264; uint64_t x_265; uint64_t x_266; size_t x_267; size_t x_268; lean_object* x_269; size_t x_270; size_t x_271; size_t x_272; lean_object* x_273; lean_object* x_274; 
x_251 = lean_st_ref_get(x_7, x_8);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_47, 0);
lean_inc(x_256);
x_257 = lean_array_get_size(x_255);
x_258 = l_Lean_Name_hash___override(x_256);
x_259 = lean_unsigned_to_nat(32u);
x_260 = lean_uint64_of_nat(x_259);
x_261 = lean_uint64_shift_right(x_258, x_260);
x_262 = lean_uint64_xor(x_258, x_261);
x_263 = lean_unsigned_to_nat(16u);
x_264 = lean_uint64_of_nat(x_263);
x_265 = lean_uint64_shift_right(x_262, x_264);
x_266 = lean_uint64_xor(x_262, x_265);
x_267 = lean_uint64_to_usize(x_266);
x_268 = lean_usize_of_nat(x_257);
lean_dec(x_257);
x_269 = lean_unsigned_to_nat(1u);
x_270 = lean_usize_of_nat(x_269);
x_271 = lean_usize_sub(x_268, x_270);
x_272 = lean_usize_land(x_267, x_271);
x_273 = lean_array_uget(x_255, x_272);
lean_dec(x_255);
x_274 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_256, x_273);
lean_dec(x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; 
x_275 = l_Lean_NameMap_find_x3f(lean_box(0), x_2, x_256);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
x_276 = l___private_Lean_Environment_0__Lean_findOLeanParts(x_256, x_254);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
lean_inc(x_7);
x_217 = x_250;
x_218 = x_277;
x_219 = x_7;
x_220 = x_278;
goto block_249;
}
else
{
uint8_t x_279; 
lean_dec(x_47);
lean_dec(x_7);
x_279 = !lean_is_exclusive(x_276);
if (x_279 == 0)
{
return x_276;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_276, 0);
x_281 = lean_ctor_get(x_276, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_276);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_275, 0);
lean_inc(x_283);
lean_dec(x_275);
x_284 = l_Lean_ModuleArtifacts_oleanParts(x_283);
x_285 = l_Array_isEmpty___redArg(x_284);
if (x_285 == 0)
{
lean_dec(x_256);
lean_inc(x_7);
x_217 = x_250;
x_218 = x_284;
x_219 = x_7;
x_220 = x_254;
goto block_249;
}
else
{
lean_object* x_286; 
lean_dec(x_284);
x_286 = l___private_Lean_Environment_0__Lean_findOLeanParts(x_256, x_254);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_7);
x_217 = x_250;
x_218 = x_287;
x_219 = x_7;
x_220 = x_288;
goto block_249;
}
else
{
uint8_t x_289; 
lean_dec(x_47);
lean_dec(x_7);
x_289 = !lean_is_exclusive(x_286);
if (x_289 == 0)
{
return x_286;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_286, 0);
x_291 = lean_ctor_get(x_286, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_286);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
}
}
else
{
lean_dec(x_47);
if (x_250 == 0)
{
lean_dec(x_274);
lean_dec(x_256);
x_9 = x_18;
x_10 = x_254;
goto block_15;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_293 = lean_ctor_get(x_274, 0);
lean_inc(x_293);
lean_dec(x_274);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get_uint8(x_294, sizeof(void*)*1);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_st_ref_take(x_7, x_254);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = !lean_is_exclusive(x_296);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_296, 1);
x_301 = lean_ctor_get(x_296, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_298);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; size_t x_310; size_t x_311; size_t x_312; lean_object* x_313; uint8_t x_314; 
x_303 = lean_ctor_get(x_298, 0);
x_304 = lean_ctor_get(x_298, 1);
x_305 = lean_ctor_get(x_294, 0);
lean_inc(x_305);
x_306 = lean_ctor_get_uint8(x_294, sizeof(void*)*1 + 1);
lean_dec(x_294);
x_307 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set_uint8(x_307, sizeof(void*)*1, x_250);
lean_ctor_set_uint8(x_307, sizeof(void*)*1 + 1, x_306);
x_308 = lean_ctor_get(x_293, 1);
lean_inc(x_308);
lean_ctor_set(x_296, 1, x_308);
lean_ctor_set(x_296, 0, x_307);
x_309 = lean_array_get_size(x_304);
x_310 = lean_usize_of_nat(x_309);
lean_dec(x_309);
x_311 = lean_usize_sub(x_310, x_270);
x_312 = lean_usize_land(x_267, x_311);
x_313 = lean_array_uget(x_304, x_312);
x_314 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_256, x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_315 = lean_nat_add(x_303, x_269);
lean_dec(x_303);
x_316 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_316, 0, x_256);
lean_ctor_set(x_316, 1, x_296);
lean_ctor_set(x_316, 2, x_313);
x_317 = lean_array_uset(x_304, x_312, x_316);
x_318 = lean_unsigned_to_nat(2u);
x_319 = lean_nat_shiftl(x_315, x_318);
x_320 = lean_unsigned_to_nat(3u);
x_321 = lean_nat_div(x_319, x_320);
lean_dec(x_319);
x_322 = lean_array_get_size(x_317);
x_323 = lean_nat_dec_le(x_321, x_322);
lean_dec(x_322);
lean_dec(x_321);
if (x_323 == 0)
{
lean_object* x_324; 
x_324 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_317);
lean_ctor_set(x_298, 1, x_324);
lean_ctor_set(x_298, 0, x_315);
x_30 = x_300;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_298;
goto block_46;
}
else
{
lean_ctor_set(x_298, 1, x_317);
lean_ctor_set(x_298, 0, x_315);
x_30 = x_300;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_298;
goto block_46;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_box(0);
x_326 = lean_array_uset(x_304, x_312, x_325);
x_327 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_256, x_296, x_313);
x_328 = lean_array_uset(x_326, x_312, x_327);
lean_ctor_set(x_298, 1, x_328);
x_30 = x_300;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_298;
goto block_46;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; size_t x_336; size_t x_337; size_t x_338; lean_object* x_339; uint8_t x_340; 
x_329 = lean_ctor_get(x_298, 0);
x_330 = lean_ctor_get(x_298, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_298);
x_331 = lean_ctor_get(x_294, 0);
lean_inc(x_331);
x_332 = lean_ctor_get_uint8(x_294, sizeof(void*)*1 + 1);
lean_dec(x_294);
x_333 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*1, x_250);
lean_ctor_set_uint8(x_333, sizeof(void*)*1 + 1, x_332);
x_334 = lean_ctor_get(x_293, 1);
lean_inc(x_334);
lean_ctor_set(x_296, 1, x_334);
lean_ctor_set(x_296, 0, x_333);
x_335 = lean_array_get_size(x_330);
x_336 = lean_usize_of_nat(x_335);
lean_dec(x_335);
x_337 = lean_usize_sub(x_336, x_270);
x_338 = lean_usize_land(x_267, x_337);
x_339 = lean_array_uget(x_330, x_338);
x_340 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_256, x_339);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_341 = lean_nat_add(x_329, x_269);
lean_dec(x_329);
x_342 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_342, 0, x_256);
lean_ctor_set(x_342, 1, x_296);
lean_ctor_set(x_342, 2, x_339);
x_343 = lean_array_uset(x_330, x_338, x_342);
x_344 = lean_unsigned_to_nat(2u);
x_345 = lean_nat_shiftl(x_341, x_344);
x_346 = lean_unsigned_to_nat(3u);
x_347 = lean_nat_div(x_345, x_346);
lean_dec(x_345);
x_348 = lean_array_get_size(x_343);
x_349 = lean_nat_dec_le(x_347, x_348);
lean_dec(x_348);
lean_dec(x_347);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_343);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_341);
lean_ctor_set(x_351, 1, x_350);
x_30 = x_300;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_351;
goto block_46;
}
else
{
lean_object* x_352; 
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_341);
lean_ctor_set(x_352, 1, x_343);
x_30 = x_300;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_352;
goto block_46;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_box(0);
x_354 = lean_array_uset(x_330, x_338, x_353);
x_355 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_256, x_296, x_339);
x_356 = lean_array_uset(x_354, x_338, x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_329);
lean_ctor_set(x_357, 1, x_356);
x_30 = x_300;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_357;
goto block_46;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; size_t x_368; size_t x_369; size_t x_370; lean_object* x_371; uint8_t x_372; 
x_358 = lean_ctor_get(x_296, 1);
lean_inc(x_358);
lean_dec(x_296);
x_359 = lean_ctor_get(x_298, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_298, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_361 = x_298;
} else {
 lean_dec_ref(x_298);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_294, 0);
lean_inc(x_362);
x_363 = lean_ctor_get_uint8(x_294, sizeof(void*)*1 + 1);
lean_dec(x_294);
x_364 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set_uint8(x_364, sizeof(void*)*1, x_250);
lean_ctor_set_uint8(x_364, sizeof(void*)*1 + 1, x_363);
x_365 = lean_ctor_get(x_293, 1);
lean_inc(x_365);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_array_get_size(x_360);
x_368 = lean_usize_of_nat(x_367);
lean_dec(x_367);
x_369 = lean_usize_sub(x_368, x_270);
x_370 = lean_usize_land(x_267, x_369);
x_371 = lean_array_uget(x_360, x_370);
x_372 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_256, x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_373 = lean_nat_add(x_359, x_269);
lean_dec(x_359);
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_256);
lean_ctor_set(x_374, 1, x_366);
lean_ctor_set(x_374, 2, x_371);
x_375 = lean_array_uset(x_360, x_370, x_374);
x_376 = lean_unsigned_to_nat(2u);
x_377 = lean_nat_shiftl(x_373, x_376);
x_378 = lean_unsigned_to_nat(3u);
x_379 = lean_nat_div(x_377, x_378);
lean_dec(x_377);
x_380 = lean_array_get_size(x_375);
x_381 = lean_nat_dec_le(x_379, x_380);
lean_dec(x_380);
lean_dec(x_379);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_375);
if (lean_is_scalar(x_361)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_361;
}
lean_ctor_set(x_383, 0, x_373);
lean_ctor_set(x_383, 1, x_382);
x_30 = x_358;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_383;
goto block_46;
}
else
{
lean_object* x_384; 
if (lean_is_scalar(x_361)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_361;
}
lean_ctor_set(x_384, 0, x_373);
lean_ctor_set(x_384, 1, x_375);
x_30 = x_358;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_384;
goto block_46;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_385 = lean_box(0);
x_386 = lean_array_uset(x_360, x_370, x_385);
x_387 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_256, x_366, x_371);
x_388 = lean_array_uset(x_386, x_370, x_387);
if (lean_is_scalar(x_361)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_361;
}
lean_ctor_set(x_389, 0, x_359);
lean_ctor_set(x_389, 1, x_388);
x_30 = x_358;
x_31 = x_293;
x_32 = x_250;
x_33 = x_297;
x_34 = x_389;
goto block_46;
}
}
}
else
{
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_256);
x_9 = x_18;
x_10 = x_254;
goto block_15;
}
}
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_5, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3_spec__3(x_1, x_2, x_3, x_4, x_13, x_9, x_7, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_importModulesCore_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_box(0);
x_7 = lean_array_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3(x_2, x_3, x_1, x_7, x_9, x_6, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_importModulesCore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_importModulesCore_go(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1(x_9, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_importModulesCore_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_importModulesCore_go_spec__2(x_6, x_2, x_7, x_8, x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3_spec__3(x_9, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__3(x_9, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_importModulesCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_importModulesCore_go(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_importModulesCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_importModulesCore(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Environment_0__Lean_subsumesInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_ConstantInfo_name(x_1);
x_37 = l_Lean_ConstantInfo_name(x_2);
x_38 = lean_name_eq(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
x_3 = x_38;
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Lean_ConstantInfo_type(x_1);
x_40 = l_Lean_ConstantInfo_type(x_2);
x_41 = lean_expr_eqv(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_3 = x_41;
goto block_35;
}
block_35:
{
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_ConstantInfo_levelParams(x_1);
x_5 = l_Lean_ConstantInfo_levelParams(x_2);
x_6 = l_List_beq___at_____private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431__spec__0(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
return x_6;
}
else
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
if (x_10 == 0)
{
return x_6;
}
else
{
return x_8;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_15, 2);
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_box(0);
lean_inc(x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_beq___at_____private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431__spec__0(x_17, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_26, 2);
x_29 = lean_ctor_get(x_27, 2);
x_30 = l_List_beq___at_____private_Lean_Declaration_0__Lean_beqConstantVal____x40_Lean_Declaration___hyg_431__spec__0(x_28, x_29);
return x_30;
}
default: 
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
}
}
default: 
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_subsumesInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Environment_0__Lean_subsumesInfo(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_finalizeImport_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_finalizeImport_unsafe__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_runtime_mark_persistent(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_finalizeImport_unsafe__3(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_finalizeImport_unsafe__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_finalizeImport_unsafe__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_32; lean_object* x_33; lean_object* x_112; uint64_t x_113; lean_object* x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; lean_object* x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; size_t x_122; size_t x_123; size_t x_124; size_t x_125; size_t x_126; lean_object* x_127; lean_object* x_128; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_17, x_24);
x_26 = lean_array_uget(x_1, x_3);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_18);
x_32 = lean_array_fget(x_27, x_17);
lean_dec(x_17);
lean_dec(x_27);
x_112 = lean_array_get_size(x_23);
x_113 = l_Lean_Name_hash___override(x_26);
x_114 = lean_unsigned_to_nat(32u);
x_115 = lean_uint64_of_nat(x_114);
x_116 = lean_uint64_shift_right(x_113, x_115);
x_117 = lean_uint64_xor(x_113, x_116);
x_118 = lean_unsigned_to_nat(16u);
x_119 = lean_uint64_of_nat(x_118);
x_120 = lean_uint64_shift_right(x_117, x_119);
x_121 = lean_uint64_xor(x_117, x_120);
x_122 = lean_uint64_to_usize(x_121);
x_123 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_124 = lean_usize_of_nat(x_24);
x_125 = lean_usize_sub(x_123, x_124);
x_126 = lean_usize_land(x_122, x_125);
x_127 = lean_array_uget(x_23, x_126);
x_128 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_26, x_127);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_16);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_130 = lean_ctor_get(x_16, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_16, 0);
lean_dec(x_131);
x_132 = lean_nat_add(x_22, x_24);
lean_dec(x_22);
lean_inc(x_32);
lean_inc(x_26);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_26);
lean_ctor_set(x_133, 1, x_32);
lean_ctor_set(x_133, 2, x_127);
x_134 = lean_array_uset(x_23, x_126, x_133);
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_nat_shiftl(x_132, x_135);
x_137 = lean_unsigned_to_nat(3u);
x_138 = lean_nat_div(x_136, x_137);
lean_dec(x_136);
x_139 = lean_array_get_size(x_134);
x_140 = lean_nat_dec_le(x_138, x_139);
lean_dec(x_139);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_134);
lean_ctor_set(x_16, 1, x_141);
lean_ctor_set(x_16, 0, x_132);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_128);
lean_ctor_set(x_142, 1, x_16);
x_33 = x_142;
goto block_111;
}
else
{
lean_object* x_143; 
lean_ctor_set(x_16, 1, x_134);
lean_ctor_set(x_16, 0, x_132);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_128);
lean_ctor_set(x_143, 1, x_16);
x_33 = x_143;
goto block_111;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_dec(x_16);
x_144 = lean_nat_add(x_22, x_24);
lean_dec(x_22);
lean_inc(x_32);
lean_inc(x_26);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_26);
lean_ctor_set(x_145, 1, x_32);
lean_ctor_set(x_145, 2, x_127);
x_146 = lean_array_uset(x_23, x_126, x_145);
x_147 = lean_unsigned_to_nat(2u);
x_148 = lean_nat_shiftl(x_144, x_147);
x_149 = lean_unsigned_to_nat(3u);
x_150 = lean_nat_div(x_148, x_149);
lean_dec(x_148);
x_151 = lean_array_get_size(x_146);
x_152 = lean_nat_dec_le(x_150, x_151);
lean_dec(x_151);
lean_dec(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_146);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_144);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_128);
lean_ctor_set(x_155, 1, x_154);
x_33 = x_155;
goto block_111;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_144);
lean_ctor_set(x_156, 1, x_146);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_128);
lean_ctor_set(x_157, 1, x_156);
x_33 = x_157;
goto block_111;
}
}
}
else
{
lean_object* x_158; 
lean_dec(x_127);
lean_dec(x_23);
lean_dec(x_22);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_128);
lean_ctor_set(x_158, 1, x_16);
x_33 = x_158;
goto block_111;
}
block_31:
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_6 = x_30;
x_7 = x_5;
goto block_12;
}
block_111:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_26);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_6 = x_36;
x_7 = x_5;
goto block_12;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l___private_Lean_Environment_0__Lean_subsumesInfo(x_32, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_32);
lean_dec(x_26);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_37);
x_6 = x_40;
x_7 = x_5;
goto block_12;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
x_44 = lean_array_get_size(x_43);
x_45 = l_Lean_Name_hash___override(x_26);
x_46 = lean_unsigned_to_nat(32u);
x_47 = lean_uint64_of_nat(x_46);
x_48 = lean_uint64_shift_right(x_45, x_47);
x_49 = lean_uint64_xor(x_45, x_48);
x_50 = lean_unsigned_to_nat(16u);
x_51 = lean_uint64_of_nat(x_50);
x_52 = lean_uint64_shift_right(x_49, x_51);
x_53 = lean_uint64_xor(x_49, x_52);
x_54 = lean_uint64_to_usize(x_53);
x_55 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_56 = lean_usize_of_nat(x_24);
x_57 = lean_usize_sub(x_55, x_56);
x_58 = lean_usize_land(x_54, x_57);
x_59 = lean_array_uget(x_43, x_58);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_26, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_61 = lean_nat_add(x_42, x_24);
lean_dec(x_42);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_32);
lean_ctor_set(x_62, 2, x_59);
x_63 = lean_array_uset(x_43, x_58, x_62);
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_nat_shiftl(x_61, x_64);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_div(x_65, x_66);
lean_dec(x_65);
x_68 = lean_array_get_size(x_63);
x_69 = lean_nat_dec_le(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_63);
lean_ctor_set(x_37, 1, x_70);
lean_ctor_set(x_37, 0, x_61);
x_29 = x_37;
goto block_31;
}
else
{
lean_ctor_set(x_37, 1, x_63);
lean_ctor_set(x_37, 0, x_61);
x_29 = x_37;
goto block_31;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_box(0);
x_72 = lean_array_uset(x_43, x_58, x_71);
x_73 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_26, x_32, x_59);
x_74 = lean_array_uset(x_72, x_58, x_73);
lean_ctor_set(x_37, 1, x_74);
x_29 = x_37;
goto block_31;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint64_t x_78; lean_object* x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; lean_object* x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; size_t x_91; lean_object* x_92; uint8_t x_93; 
x_75 = lean_ctor_get(x_37, 0);
x_76 = lean_ctor_get(x_37, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_37);
x_77 = lean_array_get_size(x_76);
x_78 = l_Lean_Name_hash___override(x_26);
x_79 = lean_unsigned_to_nat(32u);
x_80 = lean_uint64_of_nat(x_79);
x_81 = lean_uint64_shift_right(x_78, x_80);
x_82 = lean_uint64_xor(x_78, x_81);
x_83 = lean_unsigned_to_nat(16u);
x_84 = lean_uint64_of_nat(x_83);
x_85 = lean_uint64_shift_right(x_82, x_84);
x_86 = lean_uint64_xor(x_82, x_85);
x_87 = lean_uint64_to_usize(x_86);
x_88 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_89 = lean_usize_of_nat(x_24);
x_90 = lean_usize_sub(x_88, x_89);
x_91 = lean_usize_land(x_87, x_90);
x_92 = lean_array_uget(x_76, x_91);
x_93 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_26, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_94 = lean_nat_add(x_75, x_24);
lean_dec(x_75);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_26);
lean_ctor_set(x_95, 1, x_32);
lean_ctor_set(x_95, 2, x_92);
x_96 = lean_array_uset(x_76, x_91, x_95);
x_97 = lean_unsigned_to_nat(2u);
x_98 = lean_nat_shiftl(x_94, x_97);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_nat_div(x_98, x_99);
lean_dec(x_98);
x_101 = lean_array_get_size(x_96);
x_102 = lean_nat_dec_le(x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_96);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_103);
x_29 = x_104;
goto block_31;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_96);
x_29 = x_105;
goto block_31;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_box(0);
x_107 = lean_array_uset(x_76, x_91, x_106);
x_108 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_26, x_32, x_92);
x_109 = lean_array_uset(x_107, x_91, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_75);
lean_ctor_set(x_110, 1, x_109);
x_29 = x_110;
goto block_31;
}
}
}
}
}
}
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_13, 1);
x_15 = lean_array_uget(x_2, x_3);
x_16 = lean_array_get_size(x_14);
x_17 = l_Lean_Name_hash___override(x_15);
x_18 = lean_unsigned_to_nat(32u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_unsigned_to_nat(16u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_sub(x_27, x_29);
x_31 = lean_usize_land(x_26, x_30);
x_32 = lean_array_uget(x_14, x_31);
x_33 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_15, x_32);
lean_dec(x_32);
lean_dec(x_15);
if (lean_obj_tag(x_33) == 0)
{
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_push(x_5, x_34);
x_6 = x_35;
goto block_11;
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_finalizeImport_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_nat_dec_lt(x_3, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_le(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
return x_6;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__2_spec__2(x_1, x_2, x_10, x_11, x_6);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = l___private_Lean_Environment_0__Lean_ImportedModule_mainModule_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed), 1, 0);
x_10 = lean_mk_string_unchecked("missing data file for module ", 29, 29);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Name_toString(x_12, x_5, x_9);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_array_uset(x_3, x_2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_19, x_2, x_17);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_84; lean_object* x_91; lean_object* x_92; lean_object* x_170; uint64_t x_171; lean_object* x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; lean_object* x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; size_t x_180; size_t x_181; size_t x_182; size_t x_183; size_t x_184; lean_object* x_185; lean_object* x_186; 
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_14, x_21);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_15);
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
x_35 = lean_array_uget(x_3, x_5);
x_91 = lean_array_fget(x_20, x_14);
lean_dec(x_14);
lean_dec(x_20);
x_170 = lean_array_get_size(x_34);
x_171 = l_Lean_Name_hash___override(x_35);
x_172 = lean_unsigned_to_nat(32u);
x_173 = lean_uint64_of_nat(x_172);
x_174 = lean_uint64_shift_right(x_171, x_173);
x_175 = lean_uint64_xor(x_171, x_174);
x_176 = lean_unsigned_to_nat(16u);
x_177 = lean_uint64_of_nat(x_176);
x_178 = lean_uint64_shift_right(x_175, x_177);
x_179 = lean_uint64_xor(x_175, x_178);
x_180 = lean_uint64_to_usize(x_179);
x_181 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_182 = lean_usize_of_nat(x_21);
x_183 = lean_usize_sub(x_181, x_182);
x_184 = lean_usize_land(x_180, x_183);
x_185 = lean_array_uget(x_34, x_184);
x_186 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0___redArg(x_35, x_185);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_13);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_188 = lean_ctor_get(x_13, 1);
lean_dec(x_188);
x_189 = lean_ctor_get(x_13, 0);
lean_dec(x_189);
x_190 = lean_nat_add(x_33, x_21);
lean_dec(x_33);
lean_inc(x_91);
lean_inc(x_35);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_35);
lean_ctor_set(x_191, 1, x_91);
lean_ctor_set(x_191, 2, x_185);
x_192 = lean_array_uset(x_34, x_184, x_191);
x_193 = lean_unsigned_to_nat(2u);
x_194 = lean_nat_shiftl(x_190, x_193);
x_195 = lean_unsigned_to_nat(3u);
x_196 = lean_nat_div(x_194, x_195);
lean_dec(x_194);
x_197 = lean_array_get_size(x_192);
x_198 = lean_nat_dec_le(x_196, x_197);
lean_dec(x_197);
lean_dec(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_192);
lean_ctor_set(x_13, 1, x_199);
lean_ctor_set(x_13, 0, x_190);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_186);
lean_ctor_set(x_200, 1, x_13);
x_92 = x_200;
goto block_169;
}
else
{
lean_object* x_201; 
lean_ctor_set(x_13, 1, x_192);
lean_ctor_set(x_13, 0, x_190);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_186);
lean_ctor_set(x_201, 1, x_13);
x_92 = x_201;
goto block_169;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_13);
x_202 = lean_nat_add(x_33, x_21);
lean_dec(x_33);
lean_inc(x_91);
lean_inc(x_35);
x_203 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_203, 0, x_35);
lean_ctor_set(x_203, 1, x_91);
lean_ctor_set(x_203, 2, x_185);
x_204 = lean_array_uset(x_34, x_184, x_203);
x_205 = lean_unsigned_to_nat(2u);
x_206 = lean_nat_shiftl(x_202, x_205);
x_207 = lean_unsigned_to_nat(3u);
x_208 = lean_nat_div(x_206, x_207);
lean_dec(x_206);
x_209 = lean_array_get_size(x_204);
x_210 = lean_nat_dec_le(x_208, x_209);
lean_dec(x_209);
lean_dec(x_208);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_204);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_186);
lean_ctor_set(x_213, 1, x_212);
x_92 = x_213;
goto block_169;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_202);
lean_ctor_set(x_214, 1, x_204);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_186);
lean_ctor_set(x_215, 1, x_214);
x_92 = x_215;
goto block_169;
}
}
}
else
{
lean_object* x_216; 
lean_dec(x_185);
lean_dec(x_34);
lean_dec(x_33);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_186);
lean_ctor_set(x_216, 1, x_13);
x_92 = x_216;
goto block_169;
}
block_32:
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_usize_of_nat(x_21);
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
x_6 = x_28;
x_7 = x_25;
goto _start;
}
block_83:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; uint8_t x_57; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
x_41 = lean_array_get_size(x_40);
x_42 = l_Lean_Name_hash___override(x_35);
x_43 = lean_unsigned_to_nat(32u);
x_44 = lean_uint64_of_nat(x_43);
x_45 = lean_uint64_shift_right(x_42, x_44);
x_46 = lean_uint64_xor(x_42, x_45);
x_47 = lean_unsigned_to_nat(16u);
x_48 = lean_uint64_of_nat(x_47);
x_49 = lean_uint64_shift_right(x_46, x_48);
x_50 = lean_uint64_xor(x_46, x_49);
x_51 = lean_uint64_to_usize(x_50);
x_52 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_53 = lean_usize_of_nat(x_21);
x_54 = lean_usize_sub(x_52, x_53);
x_55 = lean_usize_land(x_51, x_54);
x_56 = lean_array_uget(x_40, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_35, x_56);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_36);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_59 = lean_ctor_get(x_36, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_36, 0);
lean_dec(x_60);
x_61 = lean_nat_add(x_39, x_21);
lean_dec(x_39);
lean_inc(x_1);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_35);
lean_ctor_set(x_62, 1, x_1);
lean_ctor_set(x_62, 2, x_56);
x_63 = lean_array_uset(x_40, x_55, x_62);
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_nat_shiftl(x_61, x_64);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_div(x_65, x_66);
lean_dec(x_65);
x_68 = lean_array_get_size(x_63);
x_69 = lean_nat_dec_le(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_63);
lean_ctor_set(x_36, 1, x_70);
lean_ctor_set(x_36, 0, x_61);
x_24 = x_37;
x_25 = x_38;
x_26 = x_36;
goto block_32;
}
else
{
lean_ctor_set(x_36, 1, x_63);
lean_ctor_set(x_36, 0, x_61);
x_24 = x_37;
x_25 = x_38;
x_26 = x_36;
goto block_32;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_36);
x_71 = lean_nat_add(x_39, x_21);
lean_dec(x_39);
lean_inc(x_1);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_35);
lean_ctor_set(x_72, 1, x_1);
lean_ctor_set(x_72, 2, x_56);
x_73 = lean_array_uset(x_40, x_55, x_72);
x_74 = lean_unsigned_to_nat(2u);
x_75 = lean_nat_shiftl(x_71, x_74);
x_76 = lean_unsigned_to_nat(3u);
x_77 = lean_nat_div(x_75, x_76);
lean_dec(x_75);
x_78 = lean_array_get_size(x_73);
x_79 = lean_nat_dec_le(x_77, x_78);
lean_dec(x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_73);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_80);
x_24 = x_37;
x_25 = x_38;
x_26 = x_81;
goto block_32;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_73);
x_24 = x_37;
x_25 = x_38;
x_26 = x_82;
goto block_32;
}
}
}
else
{
lean_dec(x_56);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_35);
x_24 = x_37;
x_25 = x_38;
x_26 = x_36;
goto block_32;
}
}
block_90:
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_84);
x_85 = l_Lean_throwAlreadyImported___redArg(x_2, x_12, x_1, x_35, x_7);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
block_169:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_36 = x_12;
x_37 = x_94;
x_38 = x_7;
goto block_83;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = l___private_Lean_Environment_0__Lean_subsumesInfo(x_91, x_96);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = l___private_Lean_Environment_0__Lean_subsumesInfo(x_96, x_91);
lean_dec(x_91);
lean_dec(x_96);
if (x_98 == 0)
{
lean_dec(x_23);
x_84 = x_95;
goto block_90;
}
else
{
if (x_97 == 0)
{
x_36 = x_12;
x_37 = x_95;
x_38 = x_7;
goto block_83;
}
else
{
lean_dec(x_23);
x_84 = x_95;
goto block_90;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_96);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; size_t x_112; size_t x_113; size_t x_114; size_t x_115; size_t x_116; lean_object* x_117; uint8_t x_118; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
x_102 = lean_array_get_size(x_101);
x_103 = l_Lean_Name_hash___override(x_35);
x_104 = lean_unsigned_to_nat(32u);
x_105 = lean_uint64_of_nat(x_104);
x_106 = lean_uint64_shift_right(x_103, x_105);
x_107 = lean_uint64_xor(x_103, x_106);
x_108 = lean_unsigned_to_nat(16u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_uint64_to_usize(x_111);
x_113 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_114 = lean_usize_of_nat(x_21);
x_115 = lean_usize_sub(x_113, x_114);
x_116 = lean_usize_land(x_112, x_115);
x_117 = lean_array_uget(x_101, x_116);
x_118 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_35, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_119 = lean_nat_add(x_100, x_21);
lean_dec(x_100);
lean_inc(x_35);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_35);
lean_ctor_set(x_120, 1, x_91);
lean_ctor_set(x_120, 2, x_117);
x_121 = lean_array_uset(x_101, x_116, x_120);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_nat_shiftl(x_119, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = lean_array_get_size(x_121);
x_127 = lean_nat_dec_le(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_121);
lean_ctor_set(x_95, 1, x_128);
lean_ctor_set(x_95, 0, x_119);
x_36 = x_12;
x_37 = x_95;
x_38 = x_7;
goto block_83;
}
else
{
lean_ctor_set(x_95, 1, x_121);
lean_ctor_set(x_95, 0, x_119);
x_36 = x_12;
x_37 = x_95;
x_38 = x_7;
goto block_83;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_box(0);
x_130 = lean_array_uset(x_101, x_116, x_129);
lean_inc(x_35);
x_131 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_35, x_91, x_117);
x_132 = lean_array_uset(x_130, x_116, x_131);
lean_ctor_set(x_95, 1, x_132);
x_36 = x_12;
x_37 = x_95;
x_38 = x_7;
goto block_83;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint64_t x_136; lean_object* x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; lean_object* x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; size_t x_145; size_t x_146; size_t x_147; size_t x_148; size_t x_149; lean_object* x_150; uint8_t x_151; 
x_133 = lean_ctor_get(x_95, 0);
x_134 = lean_ctor_get(x_95, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_95);
x_135 = lean_array_get_size(x_134);
x_136 = l_Lean_Name_hash___override(x_35);
x_137 = lean_unsigned_to_nat(32u);
x_138 = lean_uint64_of_nat(x_137);
x_139 = lean_uint64_shift_right(x_136, x_138);
x_140 = lean_uint64_xor(x_136, x_139);
x_141 = lean_unsigned_to_nat(16u);
x_142 = lean_uint64_of_nat(x_141);
x_143 = lean_uint64_shift_right(x_140, x_142);
x_144 = lean_uint64_xor(x_140, x_143);
x_145 = lean_uint64_to_usize(x_144);
x_146 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_147 = lean_usize_of_nat(x_21);
x_148 = lean_usize_sub(x_146, x_147);
x_149 = lean_usize_land(x_145, x_148);
x_150 = lean_array_uget(x_134, x_149);
x_151 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_35, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_152 = lean_nat_add(x_133, x_21);
lean_dec(x_133);
lean_inc(x_35);
x_153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_153, 0, x_35);
lean_ctor_set(x_153, 1, x_91);
lean_ctor_set(x_153, 2, x_150);
x_154 = lean_array_uset(x_134, x_149, x_153);
x_155 = lean_unsigned_to_nat(2u);
x_156 = lean_nat_shiftl(x_152, x_155);
x_157 = lean_unsigned_to_nat(3u);
x_158 = lean_nat_div(x_156, x_157);
lean_dec(x_156);
x_159 = lean_array_get_size(x_154);
x_160 = lean_nat_dec_le(x_158, x_159);
lean_dec(x_159);
lean_dec(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_154);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_152);
lean_ctor_set(x_162, 1, x_161);
x_36 = x_12;
x_37 = x_162;
x_38 = x_7;
goto block_83;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_154);
x_36 = x_12;
x_37 = x_163;
x_38 = x_7;
goto block_83;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_box(0);
x_165 = lean_array_uset(x_134, x_149, x_164);
lean_inc(x_35);
x_166 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_35, x_91, x_150);
x_167 = lean_array_uset(x_165, x_149, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_133);
lean_ctor_set(x_168, 1, x_167);
x_36 = x_12;
x_37 = x_168;
x_38 = x_7;
goto block_83;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; lean_object* x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_array_uget(x_2, x_4);
x_18 = lean_array_get_size(x_16);
x_19 = l_Lean_Name_hash___override(x_17);
x_20 = lean_unsigned_to_nat(32u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_unsigned_to_nat(16u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_sub(x_29, x_31);
x_33 = lean_usize_land(x_28, x_32);
x_34 = lean_array_uget(x_16, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_17, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_37 = lean_ctor_get(x_5, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 0);
lean_dec(x_38);
x_39 = lean_nat_add(x_15, x_30);
lean_dec(x_15);
lean_inc(x_1);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_17);
lean_ctor_set(x_40, 1, x_1);
lean_ctor_set(x_40, 2, x_34);
x_41 = lean_array_uset(x_16, x_33, x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_shiftl(x_39, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_41);
lean_ctor_set(x_5, 1, x_48);
lean_ctor_set(x_5, 0, x_39);
x_7 = x_5;
goto block_12;
}
else
{
lean_ctor_set(x_5, 1, x_41);
lean_ctor_set(x_5, 0, x_39);
x_7 = x_5;
goto block_12;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_5);
x_49 = lean_nat_add(x_15, x_30);
lean_dec(x_15);
lean_inc(x_1);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_17);
lean_ctor_set(x_50, 1, x_1);
lean_ctor_set(x_50, 2, x_34);
x_51 = lean_array_uset(x_16, x_33, x_50);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_shiftl(x_49, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = lean_array_get_size(x_51);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_58);
x_7 = x_59;
goto block_12;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_51);
x_7 = x_60;
goto block_12;
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_7 = x_5;
goto block_12;
}
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_nat_dec_lt(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_array_fget(x_1, x_5);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_13);
x_16 = l_Array_toSubarray___redArg(x_13, x_14, x_15);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_size(x_17);
x_21 = lean_usize_of_nat(x_14);
lean_inc(x_5);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__5(x_5, x_2, x_17, x_20, x_21, x_19, x_6);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_12, 3);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_array_size(x_28);
lean_inc(x_5);
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6(x_5, x_28, x_29, x_21, x_27, x_25);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_ctor_set(x_24, 0, x_31);
x_33 = lean_ctor_get(x_3, 2);
x_34 = lean_nat_add(x_5, x_33);
lean_dec(x_5);
x_4 = x_24;
x_5 = x_34;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_ctor_get(x_12, 3);
lean_inc(x_38);
lean_dec(x_12);
x_39 = lean_array_size(x_38);
lean_inc(x_5);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6(x_5, x_38, x_39, x_21, x_36, x_25);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_37);
x_44 = lean_ctor_get(x_3, 2);
x_45 = lean_nat_add(x_5, x_44);
lean_dec(x_5);
x_4 = x_43;
x_5 = x_45;
x_6 = x_42;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_22);
if (x_47 == 0)
{
return x_22;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_nat_dec_lt(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_array_fget(x_2, x_5);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_13);
x_16 = l_Array_toSubarray___redArg(x_13, x_14, x_15);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_size(x_17);
x_21 = lean_usize_of_nat(x_14);
lean_inc(x_5);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__5(x_5, x_1, x_17, x_20, x_21, x_19, x_6);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_12, 3);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_array_size(x_28);
lean_inc(x_5);
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6(x_5, x_28, x_29, x_21, x_27, x_25);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_ctor_set(x_24, 0, x_31);
x_33 = lean_ctor_get(x_3, 2);
x_34 = lean_nat_add(x_5, x_33);
lean_dec(x_5);
x_35 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___redArg(x_2, x_1, x_3, x_24, x_34, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_ctor_get(x_12, 3);
lean_inc(x_38);
lean_dec(x_12);
x_39 = lean_array_size(x_38);
lean_inc(x_5);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6(x_5, x_38, x_39, x_21, x_36, x_25);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_37);
x_44 = lean_ctor_get(x_3, 2);
x_45 = lean_nat_add(x_5, x_44);
lean_dec(x_5);
x_46 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___redArg(x_2, x_1, x_3, x_43, x_45, x_42);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_22);
if (x_47 == 0)
{
return x_22;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__9_spec__9(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = l___private_Lean_Environment_0__Lean_ImportedModule_serverData_x3f(x_13, x_1);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_array_push(x_5, x_15);
x_6 = x_16;
goto block_11;
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_finalizeImport_spec__9(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_nat_dec_lt(x_3, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_le(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
return x_6;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__9_spec__9(x_1, x_2, x_10, x_11, x_6);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__0(x_8, x_10, x_7);
x_12 = l_Array_append(lean_box(0), x_4, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__0(x_8, x_10, x_7);
x_12 = l_Array_append(lean_box(0), x_4, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_16 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11_spec__11(x_1, x_15, x_3, x_12);
return x_16;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__13(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = l___private_Lean_Environment_0__Lean_ImportedModule_publicModule_x3f(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
x_6 = x_4;
x_7 = x_5;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_18);
x_21 = l_Array_toSubarray___redArg(x_18, x_19, x_20);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_4);
x_24 = lean_array_size(x_22);
x_25 = lean_usize_of_nat(x_19);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__1(x_22, x_24, x_25, x_23, x_5);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_6 = x_29;
x_7 = x_28;
goto block_12;
}
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_4, x_12);
x_5 = x_15;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_Environment_0__Lean_ImportedModule_publicModule_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_18);
lean_dec(x_4);
x_5 = x_19;
goto block_10;
}
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__16(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_finalizeImport(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; size_t x_159; lean_object* x_160; uint8_t x_161; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; size_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; size_t x_213; lean_object* x_214; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; size_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; size_t x_285; lean_object* x_286; uint8_t x_293; lean_object* x_313; uint8_t x_314; uint8_t x_315; 
x_313 = lean_box(2);
x_314 = lean_unbox(x_313);
x_315 = l_Lean_instDecidableEqOLeanLevel(x_7, x_314);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_box(1);
x_317 = lean_unbox(x_316);
x_293 = x_317;
goto block_312;
}
else
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_box(0);
x_319 = lean_unbox(x_318);
x_293 = x_319;
goto block_312;
}
block_40:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(0);
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 4);
lean_inc(x_19);
lean_inc(x_9);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_ctor_get(x_9, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_18);
lean_ctor_set(x_25, 4, x_19);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*8, x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_9, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_9, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_9, 4);
lean_inc(x_32);
lean_inc(x_9);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_26);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_ctor_get(x_9, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 7);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 3, x_31);
lean_ctor_set(x_38, 4, x_32);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_35);
lean_ctor_set(x_38, 7, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*8, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
block_52:
{
if (x_6 == 0)
{
lean_dec(x_41);
x_9 = x_42;
x_10 = x_43;
goto block_40;
}
else
{
lean_object* x_44; 
lean_inc(x_3);
x_44 = l___private_Lean_Environment_0__Lean_finalizePersistentExtensions(x_42, x_41, x_3, x_43);
if (lean_obj_tag(x_44) == 0)
{
if (x_5 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_9 = x_45;
x_10 = x_46;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_runtime_mark_persistent(x_47, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_9 = x_50;
x_10 = x_51;
goto block_40;
}
}
else
{
lean_dec(x_3);
return x_44;
}
}
}
block_146:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_62);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_60);
x_72 = lean_mk_empty_array_with_capacity(x_54);
lean_inc(x_57);
lean_inc(x_68);
lean_inc(x_2);
lean_inc(x_59);
x_73 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_2);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_68);
lean_ctor_set(x_73, 4, x_57);
lean_ctor_set_uint32(x_73, sizeof(void*)*5, x_4);
lean_ctor_set_uint8(x_73, sizeof(void*)*5 + 4, x_67);
x_74 = lean_box(0);
x_75 = lean_box(0);
x_76 = l_Lean_NameTrie_empty(lean_box(0));
lean_inc(x_54);
lean_inc(x_57);
lean_inc(x_61);
x_77 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_61, x_57, x_54, x_66);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_57);
x_81 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_81, 0, x_59);
lean_ctor_set(x_81, 1, x_2);
lean_ctor_set(x_81, 2, x_70);
lean_ctor_set(x_81, 3, x_68);
lean_ctor_set(x_81, 4, x_57);
lean_ctor_set_uint32(x_81, sizeof(void*)*5, x_4);
lean_ctor_set_uint8(x_81, sizeof(void*)*5 + 4, x_67);
lean_inc(x_81);
lean_inc(x_69);
lean_inc(x_61);
lean_inc(x_55);
lean_inc(x_64);
lean_inc(x_58);
x_82 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_82, 0, x_58);
lean_ctor_set(x_82, 1, x_64);
lean_ctor_set(x_82, 2, x_55);
lean_ctor_set(x_82, 3, x_61);
lean_ctor_set(x_82, 4, x_69);
lean_ctor_set(x_82, 5, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*6, x_53);
lean_inc(x_69);
lean_inc(x_61);
lean_inc(x_55);
lean_inc(x_64);
x_83 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_64);
lean_ctor_set(x_83, 2, x_55);
lean_ctor_set(x_83, 3, x_61);
lean_ctor_set(x_83, 4, x_69);
lean_ctor_set(x_83, 5, x_73);
lean_ctor_set_uint8(x_83, sizeof(void*)*6, x_53);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_75);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_76);
lean_inc(x_82);
lean_ctor_set(x_77, 1, x_83);
lean_ctor_set(x_77, 0, x_82);
x_86 = lean_task_pure(x_82);
lean_inc(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_box(0);
x_89 = lean_box(0);
x_90 = lean_task_pure(x_84);
x_91 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_61);
lean_ctor_set(x_91, 2, x_86);
lean_ctor_set(x_91, 3, x_87);
lean_ctor_set(x_91, 4, x_88);
lean_ctor_set(x_91, 5, x_89);
lean_ctor_set(x_91, 6, x_84);
lean_ctor_set(x_91, 7, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*8, x_60);
x_92 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_92, 0, x_58);
lean_ctor_set(x_92, 1, x_64);
lean_ctor_set(x_92, 2, x_55);
lean_ctor_set(x_92, 3, x_79);
lean_ctor_set(x_92, 4, x_69);
lean_ctor_set(x_92, 5, x_81);
lean_ctor_set_uint8(x_92, sizeof(void*)*6, x_53);
x_93 = l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(x_91, x_92);
lean_dec(x_91);
x_94 = l_Array_filterMapM___at___Lean_finalizeImport_spec__9(x_7, x_63, x_54, x_65);
lean_dec(x_65);
lean_dec(x_63);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 3);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_97, x_94, x_54, x_80);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_93, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_93, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_93, 5);
lean_inc(x_104);
x_105 = lean_ctor_get(x_93, 6);
lean_inc(x_105);
x_106 = lean_ctor_get(x_93, 7);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_93, sizeof(void*)*8);
lean_dec(x_93);
x_108 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_108, 0, x_95);
lean_ctor_set(x_108, 1, x_99);
lean_ctor_set(x_108, 2, x_101);
lean_ctor_set(x_108, 3, x_102);
lean_ctor_set(x_108, 4, x_103);
lean_ctor_set(x_108, 5, x_104);
lean_ctor_set(x_108, 6, x_105);
lean_ctor_set(x_108, 7, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_107);
if (x_5 == 0)
{
x_41 = x_57;
x_42 = x_108;
x_43 = x_100;
goto block_52;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_runtime_mark_persistent(x_108, x_100);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_41 = x_57;
x_42 = x_110;
x_43 = x_111;
goto block_52;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_112 = lean_ctor_get(x_77, 0);
x_113 = lean_ctor_get(x_77, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_77);
lean_inc(x_57);
x_114 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_114, 0, x_59);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set(x_114, 2, x_70);
lean_ctor_set(x_114, 3, x_68);
lean_ctor_set(x_114, 4, x_57);
lean_ctor_set_uint32(x_114, sizeof(void*)*5, x_4);
lean_ctor_set_uint8(x_114, sizeof(void*)*5 + 4, x_67);
lean_inc(x_114);
lean_inc(x_69);
lean_inc(x_61);
lean_inc(x_55);
lean_inc(x_64);
lean_inc(x_58);
x_115 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_115, 0, x_58);
lean_ctor_set(x_115, 1, x_64);
lean_ctor_set(x_115, 2, x_55);
lean_ctor_set(x_115, 3, x_61);
lean_ctor_set(x_115, 4, x_69);
lean_ctor_set(x_115, 5, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*6, x_53);
lean_inc(x_69);
lean_inc(x_61);
lean_inc(x_55);
lean_inc(x_64);
x_116 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_116, 0, x_71);
lean_ctor_set(x_116, 1, x_64);
lean_ctor_set(x_116, 2, x_55);
lean_ctor_set(x_116, 3, x_61);
lean_ctor_set(x_116, 4, x_69);
lean_ctor_set(x_116, 5, x_73);
lean_ctor_set_uint8(x_116, sizeof(void*)*6, x_53);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_118, 0, x_74);
lean_ctor_set(x_118, 1, x_75);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_76);
lean_inc(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_116);
x_120 = lean_task_pure(x_115);
lean_inc(x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_118);
x_122 = lean_box(0);
x_123 = lean_box(0);
x_124 = lean_task_pure(x_117);
x_125 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_61);
lean_ctor_set(x_125, 2, x_120);
lean_ctor_set(x_125, 3, x_121);
lean_ctor_set(x_125, 4, x_122);
lean_ctor_set(x_125, 5, x_123);
lean_ctor_set(x_125, 6, x_117);
lean_ctor_set(x_125, 7, x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*8, x_60);
x_126 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_126, 0, x_58);
lean_ctor_set(x_126, 1, x_64);
lean_ctor_set(x_126, 2, x_55);
lean_ctor_set(x_126, 3, x_112);
lean_ctor_set(x_126, 4, x_69);
lean_ctor_set(x_126, 5, x_114);
lean_ctor_set_uint8(x_126, sizeof(void*)*6, x_53);
x_127 = l___private_Lean_Environment_0__Lean_Environment_setCheckedSync(x_125, x_126);
lean_dec(x_125);
x_128 = l_Array_filterMapM___at___Lean_finalizeImport_spec__9(x_7, x_63, x_54, x_65);
lean_dec(x_65);
lean_dec(x_63);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 3);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l___private_Lean_Environment_0__Lean_setImportedEntries(x_131, x_128, x_54, x_113);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_127, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_127, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 5);
lean_inc(x_138);
x_139 = lean_ctor_get(x_127, 6);
lean_inc(x_139);
x_140 = lean_ctor_get(x_127, 7);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_127, sizeof(void*)*8);
lean_dec(x_127);
x_142 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_142, 0, x_129);
lean_ctor_set(x_142, 1, x_133);
lean_ctor_set(x_142, 2, x_135);
lean_ctor_set(x_142, 3, x_136);
lean_ctor_set(x_142, 4, x_137);
lean_ctor_set(x_142, 5, x_138);
lean_ctor_set(x_142, 6, x_139);
lean_ctor_set(x_142, 7, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*8, x_141);
if (x_5 == 0)
{
x_41 = x_57;
x_42 = x_142;
x_43 = x_134;
goto block_52;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_runtime_mark_persistent(x_142, x_134);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_41 = x_57;
x_42 = x_144;
x_43 = x_145;
goto block_52;
}
}
}
block_172:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_162 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_152);
x_165 = lean_box(0);
x_166 = lean_box(0);
x_167 = l_Array_empty(lean_box(0));
x_168 = lean_nat_dec_lt(x_147, x_156);
if (x_168 == 0)
{
x_53 = x_161;
x_54 = x_147;
x_55 = x_148;
x_56 = x_149;
x_57 = x_150;
x_58 = x_151;
x_59 = x_166;
x_60 = x_152;
x_61 = x_153;
x_62 = x_154;
x_63 = x_155;
x_64 = x_164;
x_65 = x_156;
x_66 = x_157;
x_67 = x_158;
x_68 = x_160;
x_69 = x_165;
x_70 = x_167;
goto block_146;
}
else
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_156, x_156);
if (x_169 == 0)
{
x_53 = x_161;
x_54 = x_147;
x_55 = x_148;
x_56 = x_149;
x_57 = x_150;
x_58 = x_151;
x_59 = x_166;
x_60 = x_152;
x_61 = x_153;
x_62 = x_154;
x_63 = x_155;
x_64 = x_164;
x_65 = x_156;
x_66 = x_157;
x_67 = x_158;
x_68 = x_160;
x_69 = x_165;
x_70 = x_167;
goto block_146;
}
else
{
size_t x_170; lean_object* x_171; 
x_170 = lean_usize_of_nat(x_156);
x_171 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11(x_155, x_159, x_170, x_167);
x_53 = x_161;
x_54 = x_147;
x_55 = x_148;
x_56 = x_149;
x_57 = x_150;
x_58 = x_151;
x_59 = x_166;
x_60 = x_152;
x_61 = x_153;
x_62 = x_154;
x_63 = x_155;
x_64 = x_164;
x_65 = x_156;
x_66 = x_157;
x_67 = x_158;
x_68 = x_160;
x_69 = x_165;
x_70 = x_171;
goto block_146;
}
}
}
block_202:
{
lean_object* x_184; 
x_184 = l_Lean_EnvExtension_mkInitialExtStates(x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_192; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_box(0);
x_188 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
lean_inc(x_189);
x_190 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_190, 0, x_175);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_unbox(x_187);
lean_ctor_set_uint8(x_190, sizeof(void*)*2, x_191);
x_192 = l_Array_isEmpty___redArg(x_2);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; uint8_t x_195; 
x_193 = lean_box(1);
x_194 = lean_unbox(x_187);
x_195 = lean_unbox(x_193);
x_147 = x_173;
x_148 = x_174;
x_149 = x_182;
x_150 = x_177;
x_151 = x_190;
x_152 = x_194;
x_153 = x_185;
x_154 = x_189;
x_155 = x_176;
x_156 = x_178;
x_157 = x_186;
x_158 = x_179;
x_159 = x_181;
x_160 = x_180;
x_161 = x_195;
goto block_172;
}
else
{
uint8_t x_196; uint8_t x_197; 
x_196 = lean_unbox(x_187);
x_197 = lean_unbox(x_187);
x_147 = x_173;
x_148 = x_174;
x_149 = x_182;
x_150 = x_177;
x_151 = x_190;
x_152 = x_196;
x_153 = x_185;
x_154 = x_189;
x_155 = x_176;
x_156 = x_178;
x_157 = x_186;
x_158 = x_179;
x_159 = x_181;
x_160 = x_180;
x_161 = x_197;
goto block_172;
}
}
else
{
uint8_t x_198; 
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_3);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_184);
if (x_198 == 0)
{
return x_184;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_184, 0);
x_200 = lean_ctor_get(x_184, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_184);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
block_219:
{
size_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_array_size(x_214);
x_216 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__13(x_214, x_215, x_213, x_209, x_211);
lean_dec(x_214);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_173 = x_203;
x_174 = x_205;
x_175 = x_204;
x_176 = x_207;
x_177 = x_206;
x_178 = x_208;
x_179 = x_210;
x_180 = x_212;
x_181 = x_213;
x_182 = x_217;
x_183 = x_218;
goto block_202;
}
block_277:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_231 = lean_nat_add(x_221, x_230);
x_232 = lean_unsigned_to_nat(2u);
x_233 = lean_nat_shiftl(x_231, x_232);
lean_dec(x_231);
x_234 = lean_unsigned_to_nat(3u);
x_235 = lean_nat_div(x_233, x_234);
lean_dec(x_233);
x_236 = l_Nat_nextPowerOfTwo(x_235);
lean_dec(x_235);
x_237 = lean_box(0);
x_238 = lean_mk_array(x_236, x_237);
lean_inc(x_220);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_220);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_nat_shiftl(x_221, x_232);
lean_dec(x_221);
x_241 = lean_nat_div(x_240, x_234);
lean_dec(x_240);
x_242 = l_Nat_nextPowerOfTwo(x_241);
lean_dec(x_241);
x_243 = lean_mk_array(x_242, x_237);
lean_inc(x_220);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_220);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_nat_shiftl(x_230, x_232);
lean_dec(x_230);
x_246 = lean_nat_div(x_245, x_234);
lean_dec(x_245);
x_247 = lean_unsigned_to_nat(1u);
lean_inc(x_220);
x_248 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_248, 0, x_220);
lean_ctor_set(x_248, 1, x_227);
lean_ctor_set(x_248, 2, x_247);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_239);
lean_ctor_set(x_249, 1, x_244);
lean_inc(x_220);
x_250 = l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___redArg(x_1, x_223, x_248, x_249, x_220, x_225);
lean_dec(x_248);
lean_dec(x_1);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = !lean_is_exclusive(x_251);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_251, 0);
x_255 = lean_ctor_get(x_251, 1);
x_256 = l_Nat_nextPowerOfTwo(x_246);
lean_dec(x_246);
x_257 = lean_mk_array(x_256, x_237);
lean_inc(x_220);
lean_ctor_set(x_251, 1, x_257);
lean_ctor_set(x_251, 0, x_220);
if (x_226 == 0)
{
x_173 = x_220;
x_174 = x_254;
x_175 = x_255;
x_176 = x_222;
x_177 = x_223;
x_178 = x_224;
x_179 = x_226;
x_180 = x_229;
x_181 = x_228;
x_182 = x_251;
x_183 = x_252;
goto block_202;
}
else
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_mk_empty_array_with_capacity(x_220);
x_259 = lean_nat_dec_lt(x_220, x_224);
if (x_259 == 0)
{
x_203 = x_220;
x_204 = x_255;
x_205 = x_254;
x_206 = x_223;
x_207 = x_222;
x_208 = x_224;
x_209 = x_251;
x_210 = x_226;
x_211 = x_252;
x_212 = x_229;
x_213 = x_228;
x_214 = x_258;
goto block_219;
}
else
{
uint8_t x_260; 
x_260 = lean_nat_dec_le(x_224, x_224);
if (x_260 == 0)
{
x_203 = x_220;
x_204 = x_255;
x_205 = x_254;
x_206 = x_223;
x_207 = x_222;
x_208 = x_224;
x_209 = x_251;
x_210 = x_226;
x_211 = x_252;
x_212 = x_229;
x_213 = x_228;
x_214 = x_258;
goto block_219;
}
else
{
size_t x_261; lean_object* x_262; 
x_261 = lean_usize_of_nat(x_224);
x_262 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__14(x_222, x_228, x_261, x_258);
x_203 = x_220;
x_204 = x_255;
x_205 = x_254;
x_206 = x_223;
x_207 = x_222;
x_208 = x_224;
x_209 = x_251;
x_210 = x_226;
x_211 = x_252;
x_212 = x_229;
x_213 = x_228;
x_214 = x_262;
goto block_219;
}
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_251, 0);
x_264 = lean_ctor_get(x_251, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_251);
x_265 = l_Nat_nextPowerOfTwo(x_246);
lean_dec(x_246);
x_266 = lean_mk_array(x_265, x_237);
lean_inc(x_220);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_220);
lean_ctor_set(x_267, 1, x_266);
if (x_226 == 0)
{
x_173 = x_220;
x_174 = x_263;
x_175 = x_264;
x_176 = x_222;
x_177 = x_223;
x_178 = x_224;
x_179 = x_226;
x_180 = x_229;
x_181 = x_228;
x_182 = x_267;
x_183 = x_252;
goto block_202;
}
else
{
lean_object* x_268; uint8_t x_269; 
x_268 = lean_mk_empty_array_with_capacity(x_220);
x_269 = lean_nat_dec_lt(x_220, x_224);
if (x_269 == 0)
{
x_203 = x_220;
x_204 = x_264;
x_205 = x_263;
x_206 = x_223;
x_207 = x_222;
x_208 = x_224;
x_209 = x_267;
x_210 = x_226;
x_211 = x_252;
x_212 = x_229;
x_213 = x_228;
x_214 = x_268;
goto block_219;
}
else
{
uint8_t x_270; 
x_270 = lean_nat_dec_le(x_224, x_224);
if (x_270 == 0)
{
x_203 = x_220;
x_204 = x_264;
x_205 = x_263;
x_206 = x_223;
x_207 = x_222;
x_208 = x_224;
x_209 = x_267;
x_210 = x_226;
x_211 = x_252;
x_212 = x_229;
x_213 = x_228;
x_214 = x_268;
goto block_219;
}
else
{
size_t x_271; lean_object* x_272; 
x_271 = lean_usize_of_nat(x_224);
x_272 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__14(x_222, x_228, x_271, x_268);
x_203 = x_220;
x_204 = x_264;
x_205 = x_263;
x_206 = x_223;
x_207 = x_222;
x_208 = x_224;
x_209 = x_267;
x_210 = x_226;
x_211 = x_252;
x_212 = x_229;
x_213 = x_228;
x_214 = x_272;
goto block_219;
}
}
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_246);
lean_dec(x_229);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_3);
lean_dec(x_2);
x_273 = !lean_is_exclusive(x_250);
if (x_273 == 0)
{
return x_250;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_250, 0);
x_275 = lean_ctor_get(x_250, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_250);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
block_292:
{
lean_object* x_287; uint8_t x_288; 
x_287 = lean_array_get_size(x_280);
x_288 = lean_nat_dec_lt(x_278, x_287);
if (x_288 == 0)
{
lean_inc(x_278);
x_220 = x_278;
x_221 = x_286;
x_222 = x_280;
x_223 = x_279;
x_224 = x_287;
x_225 = x_281;
x_226 = x_283;
x_227 = x_282;
x_228 = x_285;
x_229 = x_284;
x_230 = x_278;
goto block_277;
}
else
{
uint8_t x_289; 
x_289 = lean_nat_dec_le(x_287, x_287);
if (x_289 == 0)
{
lean_inc(x_278);
x_220 = x_278;
x_221 = x_286;
x_222 = x_280;
x_223 = x_279;
x_224 = x_287;
x_225 = x_281;
x_226 = x_283;
x_227 = x_282;
x_228 = x_285;
x_229 = x_284;
x_230 = x_278;
goto block_277;
}
else
{
size_t x_290; lean_object* x_291; 
x_290 = lean_usize_of_nat(x_287);
lean_inc(x_278);
x_291 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__15(x_280, x_285, x_290, x_278);
x_220 = x_278;
x_221 = x_286;
x_222 = x_280;
x_223 = x_279;
x_224 = x_287;
x_225 = x_281;
x_226 = x_283;
x_227 = x_282;
x_228 = x_285;
x_229 = x_284;
x_230 = x_291;
goto block_277;
}
}
}
block_312:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; size_t x_298; size_t x_299; lean_object* x_300; 
x_294 = lean_ctor_get(x_1, 1);
lean_inc(x_294);
x_295 = lean_unsigned_to_nat(0u);
x_296 = lean_array_get_size(x_294);
x_297 = l_Array_filterMapM___at___Lean_finalizeImport_spec__2(x_1, x_294, x_295, x_296);
lean_dec(x_296);
x_298 = lean_array_size(x_297);
x_299 = lean_usize_of_nat(x_295);
lean_inc(x_297);
x_300 = l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__4(x_298, x_299, x_297, x_8);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_array_get_size(x_301);
x_304 = lean_nat_dec_lt(x_295, x_303);
if (x_304 == 0)
{
x_278 = x_295;
x_279 = x_301;
x_280 = x_297;
x_281 = x_302;
x_282 = x_303;
x_283 = x_293;
x_284 = x_294;
x_285 = x_299;
x_286 = x_295;
goto block_292;
}
else
{
uint8_t x_305; 
x_305 = lean_nat_dec_le(x_303, x_303);
if (x_305 == 0)
{
x_278 = x_295;
x_279 = x_301;
x_280 = x_297;
x_281 = x_302;
x_282 = x_303;
x_283 = x_293;
x_284 = x_294;
x_285 = x_299;
x_286 = x_295;
goto block_292;
}
else
{
size_t x_306; lean_object* x_307; 
x_306 = lean_usize_of_nat(x_303);
x_307 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__16(x_301, x_299, x_306, x_295);
x_278 = x_295;
x_279 = x_301;
x_280 = x_297;
x_281 = x_302;
x_282 = x_303;
x_283 = x_293;
x_284 = x_294;
x_285 = x_299;
x_286 = x_307;
goto block_292;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_297);
lean_dec(x_294);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_300);
if (x_308 == 0)
{
return x_300;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_300, 0);
x_310 = lean_ctor_get(x_300, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_300);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__2_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_finalizeImport_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at___Lean_finalizeImport_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_finalizeImport_spec__4(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__5(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__6(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at___Lean_finalizeImport_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_finalizeImport_spec__9_spec__9(x_6, x_2, x_7, x_8, x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_finalizeImport_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Array_filterMapM___at___Lean_finalizeImport_spec__9(x_5, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11_spec__11(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__11(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_finalizeImport_spec__13(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__14(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__15(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_finalizeImport_spec__16(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_finalizeImport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_Lean_finalizeImport(x_1, x_2, x_3, x_9, x_10, x_11, x_12, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModules_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_8 = lean_box(0);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
if (x_6 == 0)
{
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_mk_string_unchecked("import failed, trying to import module with anonymous name", 58, 58);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
else
{
lean_dec(x_15);
goto block_13;
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_importModules_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_load_plugin(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_importModules___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint32_t x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, size_t x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_43; 
x_43 = lean_nat_dec_lt(x_1, x_9);
if (x_43 == 0)
{
lean_dec(x_12);
x_14 = x_13;
goto block_42;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_9, x_9);
if (x_44 == 0)
{
lean_dec(x_12);
x_14 = x_13;
goto block_42;
}
else
{
size_t x_45; lean_object* x_46; 
x_45 = lean_usize_of_nat(x_9);
x_46 = l_Array_foldlMUnsafe_fold___at___Lean_importModules_spec__1(x_10, x_11, x_45, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_14 = x_47;
goto block_42;
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
block_42:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_15 = lean_unsigned_to_nat(8u);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_shiftl(x_15, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_div(x_17, x_18);
lean_dec(x_17);
x_20 = l_Nat_nextPowerOfTwo(x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_mk_array(x_20, x_21);
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_empty_array_with_capacity(x_1);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_st_mk_ref(x_25, x_14);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(2);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_instDecidableEqOLeanLevel(x_2, x_30);
lean_inc(x_27);
x_32 = l_Lean_importModulesCore(x_3, x_31, x_4, x_27, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_27, x_33);
lean_dec(x_27);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_finalizeImport(x_35, x_3, x_5, x_6, x_7, x_8, x_2, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_importModules___lam__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, uint32_t x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_importModules_spec__0(x_1, x_2, x_3, x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_array_get_size(x_5);
x_17 = lean_box(x_7);
x_18 = lean_box_uint32(x_10);
x_19 = lean_box(x_11);
x_20 = lean_box(x_12);
x_21 = lean_box_usize(x_3);
x_22 = lean_alloc_closure((void*)(l_Lean_importModules___lam__0___boxed), 13, 12);
lean_closure_set(x_22, 0, x_6);
lean_closure_set(x_22, 1, x_17);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_8);
lean_closure_set(x_22, 4, x_9);
lean_closure_set(x_22, 5, x_18);
lean_closure_set(x_22, 6, x_19);
lean_closure_set(x_22, 7, x_20);
lean_closure_set(x_22, 8, x_16);
lean_closure_set(x_22, 9, x_5);
lean_closure_set(x_22, 10, x_21);
lean_closure_set(x_22, 11, x_4);
x_23 = l_Lean_withImporting___redArg(x_22, x_15);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_importModules(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_mk_string_unchecked("import", 6, 6);
x_11 = lean_box(0);
x_12 = lean_array_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_box_usize(x_12);
x_16 = lean_box_usize(x_14);
x_17 = lean_box(x_7);
x_18 = lean_box_uint32(x_3);
x_19 = lean_box(x_5);
x_20 = lean_box(x_6);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_importModules___lam__1___boxed), 13, 12);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_16);
lean_closure_set(x_21, 3, x_11);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_13);
lean_closure_set(x_21, 6, x_17);
lean_closure_set(x_21, 7, x_8);
lean_closure_set(x_21, 8, x_2);
lean_closure_set(x_21, 9, x_18);
lean_closure_set(x_21, 10, x_19);
lean_closure_set(x_21, 11, x_20);
x_22 = lean_box(0);
x_23 = l_Lean_profileitIOUnsafe___redArg(x_10, x_2, x_21, x_22, x_9);
lean_dec(x_2);
lean_dec(x_10);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_importModules_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_importModules_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_importModules_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_importModules_spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_importModules___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint32_t x_15; uint8_t x_16; uint8_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox_uint32(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_19 = l_Lean_importModules___lam__0(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_17, x_9, x_10, x_18, x_12, x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_importModules___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; uint8_t x_16; uint32_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = lean_unbox_uint32(x_10);
lean_dec(x_10);
x_18 = lean_unbox(x_11);
lean_dec(x_11);
x_19 = lean_unbox(x_12);
lean_dec(x_12);
x_20 = l_Lean_importModules___lam__1(x_1, x_14, x_15, x_4, x_5, x_6, x_16, x_8, x_9, x_17, x_18, x_19, x_13);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_importModules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint32_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_importModules(x_1, x_2, x_10, x_4, x_11, x_12, x_13, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withImportModules___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_box(0);
x_9 = lean_box(2);
x_10 = lean_box(0);
x_11 = lean_unbox(x_8);
x_12 = lean_unbox(x_8);
x_13 = lean_unbox(x_9);
x_14 = l_Lean_importModules(x_1, x_2, x_4, x_7, x_11, x_12, x_13, x_10, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = lean_apply_2(x_3, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_environment_free_regions(x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_environment_free_regions(x_15, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_29);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withImportModules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_withImportModules___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withImportModules___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_7 = l_Lean_withImportModules___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withImportModules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_8 = l_Lean_withImportModules(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_enableDiag___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Kernel_Environment_enableDiag(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_enableDiag(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Kernel_enableDiag___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_enableDiag___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Kernel_enableDiag___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_enableDiag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Kernel_enableDiag(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Kernel_Environment_isDiagnosticsEnabled(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_isDiagnosticsEnabled___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Kernel_isDiagnosticsEnabled(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_resetDiag___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Kernel_Environment_resetDiag(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_resetDiag(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Kernel_resetDiag___lam__0___boxed), 1, 0);
x_3 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_resetDiag___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Kernel_resetDiag___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_getDiagnostics(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_task_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_setDiagnostics___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_kernel_set_diag(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_setDiagnostics(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Kernel_setDiagnostics___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l___private_Lean_Environment_0__Lean_Environment_modifyCheckedAsync(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_foldl___at_____private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_22; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
x_22 = l___private_Lean_Environment_0__Lean_looksLikeOldCodegenName(x_4);
if (x_22 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_24; 
lean_inc(x_1);
x_24 = lean_environment_find(x_1, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_26 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_27 = lean_unsigned_to_nat(21u);
x_28 = lean_unsigned_to_nat(14u);
x_29 = lean_mk_string_unchecked("value is none", 13, 13);
x_30 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_29);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
x_31 = l_panic___at_____private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo_spec__0(x_30);
x_7 = x_31;
goto block_21;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_7 = x_32;
goto block_21;
}
}
block_21:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = l_Lean_AsyncConstantInfo_ofConstantInfo(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = l_Lean_NameTrie_empty(lean_box(0));
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
if (lean_is_scalar(x_6)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_6;
 lean_ctor_set_tag(x_16, 0);
}
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_task_pure(x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_18, 2, x_17);
x_19 = l___private_Lean_Environment_0__Lean_AsyncConsts_add(x_2, x_18);
x_2 = x_19;
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_22; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
x_22 = l___private_Lean_Environment_0__Lean_looksLikeOldCodegenName(x_4);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_4);
x_23 = l_List_foldl___at___List_foldl___at_____private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd_spec__0_spec__0(x_1, x_2, x_5);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_1);
x_24 = lean_environment_find(x_1, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_26 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_27 = lean_unsigned_to_nat(21u);
x_28 = lean_unsigned_to_nat(14u);
x_29 = lean_mk_string_unchecked("value is none", 13, 13);
x_30 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_25, x_26, x_27, x_28, x_29);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
x_31 = l_panic___at_____private_Lean_Environment_0__Lean_Environment_mkFallbackConstInfo_spec__0(x_30);
x_7 = x_31;
goto block_21;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_7 = x_32;
goto block_21;
}
}
block_21:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_AsyncConstantInfo_ofConstantInfo(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_instImpl____x40_Lean_Environment___hyg_1873_;
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = l_Lean_NameTrie_empty(lean_box(0));
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
if (lean_is_scalar(x_6)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_6;
 lean_ctor_set_tag(x_16, 0);
}
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_task_pure(x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_9);
lean_ctor_set(x_18, 2, x_17);
x_19 = l___private_Lean_Environment_0__Lean_AsyncConsts_add(x_2, x_18);
x_20 = l_List_foldl___at___List_foldl___at_____private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd_spec__0_spec__0(x_1, x_19, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Declaration_getNames(x_1);
x_5 = l_List_foldl___at_____private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd_spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_elab_environment_update_base_after_kernel_add(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_Environment_updateBaseAfterKernelAdd___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_task_pure(x_2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = l___private_Lean_Environment_0__Lean_VisibilityMap_map___redArg(x_8, x_4);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 7);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_9);
lean_ctor_set(x_15, 4, x_10);
lean_ctor_set(x_15, 5, x_11);
lean_ctor_set(x_15, 6, x_12);
lean_ctor_set(x_15, 7, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*8, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_Environment_displayStats_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed), 1, 0);
x_6 = lean_mk_string_unchecked(", ", 2, 2);
x_7 = lean_string_append(x_1, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_8, x_10, x_5);
x_12 = lean_string_append(x_7, x_11);
lean_dec(x_11);
x_1 = x_12;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lean_Environment_displayStats_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_6 = lean_mk_string_unchecked("[", 1, 1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Name_toString(x_7, x_9, x_5);
x_11 = lean_string_append(x_6, x_10);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked("]", 1, 1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_16 = lean_mk_string_unchecked("[", 1, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Name_toString(x_17, x_19, x_15);
x_21 = lean_string_append(x_16, x_20);
lean_dec(x_20);
x_22 = l_List_foldl___at___List_toString___at___Lean_Environment_displayStats_spec__0_spec__0(x_21, x_3);
x_23 = lean_unsigned_to_nat(93u);
x_24 = l_Char_ofNat(x_23);
x_25 = lean_string_push(x_22, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at___Lean_Environment_displayStats_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stdout(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 4);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___Lean_Environment_displayStats_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(10u);
x_4 = l_Char_ofNat(x_3);
x_5 = lean_string_push(x_1, x_4);
x_6 = l_IO_print___at___IO_println___at___Lean_Environment_displayStats_spec__2_spec__2(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_eq(x_3, x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_23 = lean_box(x_22);
x_24 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_array_uget(x_2, x_3);
x_26 = lean_mk_string_unchecked("extension '", 11, 11);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_Name_toString(x_27, x_29, x_24);
x_31 = lean_string_append(x_26, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("'", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_33, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_51; uint8_t x_52; uint8_t x_68; lean_object* x_69; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Lean_instInhabitedEnvExtensionState;
x_38 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
x_68 = lean_ctor_get_uint8(x_51, sizeof(void*)*3);
x_69 = lean_box(x_68);
if (lean_obj_tag(x_69) == 3)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_box(0);
x_71 = lean_unbox(x_70);
x_52 = x_71;
goto block_67;
}
else
{
lean_dec(x_69);
x_52 = x_68;
goto block_67;
}
block_50:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_mk_string_unchecked("  number of imported entries: ", 30, 30);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_39, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
x_15 = x_41;
x_16 = x_42;
x_17 = x_39;
goto block_21;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
x_15 = x_41;
x_16 = x_42;
x_17 = x_39;
goto block_21;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = lean_usize_of_nat(x_39);
x_48 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_49 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__4(x_43, x_47, x_48, x_39);
lean_dec(x_43);
x_15 = x_41;
x_16 = x_42;
x_17 = x_49;
goto block_21;
}
}
}
block_67:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_inc(x_1);
x_53 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_38, x_51, x_1, x_52);
lean_dec(x_51);
x_54 = lean_ctor_get(x_25, 6);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
x_56 = lean_apply_1(x_54, x_55);
x_57 = l_Std_Format_isNil(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_mk_string_unchecked("  ", 2, 2);
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_nat_to_int(x_59);
if (lean_is_scalar(x_36)) {
 x_61 = lean_alloc_ctor(4, 2, 0);
} else {
 x_61 = x_36;
 lean_ctor_set_tag(x_61, 4);
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
x_62 = lean_unsigned_to_nat(120u);
x_63 = lean_format_pretty(x_61, x_62, x_39, x_39);
x_64 = lean_string_append(x_58, x_63);
lean_dec(x_63);
x_65 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_64, x_35);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_40 = x_53;
x_41 = x_66;
goto block_50;
}
else
{
lean_dec(x_53);
x_7 = x_65;
goto block_14;
}
}
else
{
lean_dec(x_56);
lean_dec(x_36);
x_40 = x_53;
x_41 = x_35;
goto block_50;
}
}
}
else
{
lean_dec(x_25);
x_7 = x_34;
goto block_14;
}
}
else
{
lean_object* x_72; 
lean_dec(x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_6);
return x_72;
}
block_14:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_8;
x_6 = x_9;
goto _start;
}
else
{
lean_dec(x_1);
return x_7;
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l___private_Init_Data_Repr_0__Nat_reprFast(x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
x_20 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_19, x_15);
x_7 = x_20;
goto block_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_eq(x_3, x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_23 = lean_box(x_22);
x_24 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_array_uget(x_2, x_3);
x_26 = lean_mk_string_unchecked("extension '", 11, 11);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_Name_toString(x_27, x_29, x_24);
x_31 = lean_string_append(x_26, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("'", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_33, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_51; uint8_t x_52; uint8_t x_68; lean_object* x_69; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = l_Lean_instInhabitedEnvExtensionState;
x_38 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_37);
x_39 = lean_unsigned_to_nat(0u);
x_51 = lean_ctor_get(x_25, 0);
lean_inc(x_51);
x_68 = lean_ctor_get_uint8(x_51, sizeof(void*)*3);
x_69 = lean_box(x_68);
if (lean_obj_tag(x_69) == 3)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_box(0);
x_71 = lean_unbox(x_70);
x_52 = x_71;
goto block_67;
}
else
{
lean_dec(x_69);
x_52 = x_68;
goto block_67;
}
block_50:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_mk_string_unchecked("  number of imported entries: ", 30, 30);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_39, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
x_15 = x_41;
x_16 = x_42;
x_17 = x_39;
goto block_21;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
x_15 = x_41;
x_16 = x_42;
x_17 = x_39;
goto block_21;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = lean_usize_of_nat(x_39);
x_48 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_49 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__4(x_43, x_47, x_48, x_39);
lean_dec(x_43);
x_15 = x_41;
x_16 = x_42;
x_17 = x_49;
goto block_21;
}
}
}
block_67:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_inc(x_1);
x_53 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_38, x_51, x_1, x_52);
lean_dec(x_51);
x_54 = lean_ctor_get(x_25, 6);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
x_56 = lean_apply_1(x_54, x_55);
x_57 = l_Std_Format_isNil(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_mk_string_unchecked("  ", 2, 2);
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_nat_to_int(x_59);
if (lean_is_scalar(x_36)) {
 x_61 = lean_alloc_ctor(4, 2, 0);
} else {
 x_61 = x_36;
 lean_ctor_set_tag(x_61, 4);
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
x_62 = lean_unsigned_to_nat(120u);
x_63 = lean_format_pretty(x_61, x_62, x_39, x_39);
x_64 = lean_string_append(x_58, x_63);
lean_dec(x_63);
x_65 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_64, x_35);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_40 = x_53;
x_41 = x_66;
goto block_50;
}
else
{
lean_dec(x_53);
x_7 = x_65;
goto block_14;
}
}
else
{
lean_dec(x_56);
lean_dec(x_36);
x_40 = x_53;
x_41 = x_35;
goto block_50;
}
}
}
else
{
lean_dec(x_25);
x_7 = x_34;
goto block_14;
}
}
else
{
lean_object* x_72; 
lean_dec(x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_6);
return x_72;
}
block_14:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7_spec__7(x_1, x_2, x_12, x_4, x_8, x_9);
return x_13;
}
else
{
lean_dec(x_1);
return x_7;
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l___private_Init_Data_Repr_0__Nat_reprFast(x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
x_20 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_19, x_15);
x_7 = x_20;
goto block_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_14 = lean_compacted_region_is_memory_mapped(x_13);
if (x_14 == 0)
{
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box_usize(x_13);
x_16 = lean_array_push(x_4, x_15);
x_5 = x_16;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_displayStats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_mk_string_unchecked("direct imports:                        ", 39, 39);
x_8 = l_Lean_Environment_header(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_mk_string_unchecked("#", 1, 1);
x_11 = lean_array_to_list(x_9);
x_12 = l_List_toString___at___Lean_Environment_displayStats_spec__0(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec(x_12);
x_14 = lean_string_append(x_7, x_13);
lean_dec(x_13);
x_15 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_14, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("number of imported modules:            ", 39, 39);
x_18 = lean_ctor_get(x_8, 2);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
lean_inc(x_19);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_21, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_75; uint8_t x_76; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("number of memory-mapped modules:       ", 39, 39);
x_25 = lean_unsigned_to_nat(0u);
x_75 = lean_mk_empty_array_with_capacity(x_25);
x_76 = lean_nat_dec_lt(x_25, x_19);
if (x_76 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
x_26 = x_75;
goto block_74;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_19, x_19);
if (x_77 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
x_26 = x_75;
goto block_74;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; 
x_78 = lean_usize_of_nat(x_25);
x_79 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_80 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__9(x_18, x_78, x_79, x_75);
lean_dec(x_18);
x_26 = x_80;
goto block_74;
}
}
block_74:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_29 = lean_string_append(x_24, x_28);
lean_dec(x_28);
x_30 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_29, x_23);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("number of buckets for imported consts: ", 39, 39);
lean_inc(x_1);
x_33 = l_Lean_Environment_constants(x_1);
x_34 = l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___redArg(x_33);
lean_dec(x_33);
x_35 = l___private_Init_Data_Repr_0__Nat_reprFast(x_34);
x_36 = lean_string_append(x_32, x_35);
lean_dec(x_35);
x_37 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_36, x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint32_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_mk_string_unchecked("trust level:                           ", 39, 39);
x_40 = lean_ctor_get_uint32(x_8, sizeof(void*)*5);
lean_dec(x_8);
x_41 = lean_uint32_to_nat(x_40);
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_41);
x_43 = lean_string_append(x_39, x_42);
lean_dec(x_42);
x_44 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_43, x_38);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_mk_string_unchecked("number of extensions:                  ", 39, 39);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 3);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_array_get_size(x_49);
lean_dec(x_49);
x_51 = l___private_Init_Data_Repr_0__Nat_reprFast(x_50);
x_52 = lean_string_append(x_46, x_51);
lean_dec(x_51);
x_53 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_52, x_45);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_53, 1);
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = lean_array_get_size(x_5);
x_58 = lean_box(0);
x_59 = lean_nat_dec_lt(x_25, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_53, 0, x_58);
return x_53;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_57, x_57);
if (x_60 == 0)
{
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_53, 0, x_58);
return x_53;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; 
lean_free_object(x_53);
x_61 = lean_usize_of_nat(x_25);
x_62 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_63 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7(x_1, x_5, x_61, x_62, x_58, x_55);
lean_dec(x_5);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_dec(x_53);
x_65 = lean_array_get_size(x_5);
x_66 = lean_box(0);
x_67 = lean_nat_dec_lt(x_25, x_65);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_5);
lean_dec(x_1);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_65, x_65);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_65);
lean_dec(x_5);
lean_dec(x_1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_64);
return x_70;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; 
x_71 = lean_usize_of_nat(x_25);
x_72 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_73 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7(x_1, x_5, x_71, x_72, x_66, x_64);
lean_dec(x_5);
return x_73;
}
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_53;
}
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_44;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_37;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_30;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_22;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_numBuckets___at___Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5_spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_numBuckets___at___Lean_Environment_displayStats_spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7_spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Environment_displayStats_spec__9(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_evalConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_eval_const(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_4 = lean_mk_string_unchecked("unexpected type at '", 20, 20);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_toString(x_2, x_6, x_3);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("', `", 4, 4);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Name_toString(x_1, x_11, x_3);
x_13 = lean_string_append(x_10, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("` expected", 10, 10);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts_replayKernel_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = l_Lean_instInhabitedEnvExtensionState;
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_elab_environment_to_kernel_env(x_1);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_7, x_4, x_10);
lean_dec(x_10);
x_12 = lean_elab_environment_to_kernel_env(x_2);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateImpl___redArg(x_7, x_4, x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__7(x_3, x_15);
x_17 = lean_apply_3(x_6, x_11, x_14, x_16);
x_18 = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateImpl___redArg(x_4, x_8, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts_replayKernel_unsafe__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Environment_replayConsts_replayKernel_unsafe__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Environment_replayConsts_replayKernel_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_4, x_6);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
x_8 = x_7;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 2);
lean_inc(x_22);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Environment_replayConsts_replayKernel_unsafe__1(x_1, x_2, x_3, x_16, x_7, x_18);
lean_dec(x_16);
x_24 = lean_ctor_get(x_7, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 5);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*6, x_20);
x_8 = x_26;
goto block_13;
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_6, x_10);
x_6 = x_11;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_22; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = lean_box(0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
if (x_1 == 0)
{
goto block_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_5, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_22);
x_55 = lean_environment_find(x_22, x_54);
if (lean_obj_tag(x_55) == 0)
{
goto block_52;
}
else
{
lean_object* x_56; 
lean_dec(x_55);
lean_dec(x_7);
lean_dec(x_5);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_8);
lean_ctor_set(x_56, 1, x_22);
x_2 = x_6;
x_3 = x_56;
goto _start;
}
}
block_21:
{
lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_box(0);
x_14 = lean_add_decl(x_9, x_12, x_10, x_13);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
if (lean_is_scalar(x_7)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_7;
 lean_ctor_set_tag(x_19, 0);
}
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_6;
x_3 = x_19;
goto _start;
}
}
block_52:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
lean_inc(x_23);
x_24 = l_Lean_AsyncConstantInfo_toConstantInfo(x_23);
x_25 = l_Lean_ConstantInfo_isUnsafe(x_24);
if (x_25 == 0)
{
switch (lean_obj_tag(x_24)) {
case 1:
{
uint8_t x_26; 
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
x_9 = x_22;
x_10 = x_24;
goto block_21;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_9 = x_22;
x_10 = x_28;
goto block_21;
}
}
case 2:
{
uint8_t x_29; 
lean_dec(x_23);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
x_9 = x_22;
x_10 = x_24;
goto block_21;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_9 = x_22;
x_10 = x_31;
goto block_21;
}
}
default: 
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_box(x_25);
x_33 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_importModulesCore_go_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_mk_string_unchecked("Lean.Environment", 16, 16);
x_35 = lean_mk_string_unchecked("Lean.Environment.replayConsts.replayKernel", 42, 42);
x_36 = lean_unsigned_to_nat(2159u);
x_37 = lean_unsigned_to_nat(17u);
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
x_41 = l_Lean_Name_toString(x_38, x_40, x_33);
x_42 = lean_mk_string_unchecked(" must be definition/theorem", 27, 27);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_43);
lean_dec(x_43);
lean_dec(x_35);
lean_dec(x_34);
lean_inc(x_22);
x_45 = l_panic___redArg(x_22, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_22);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_23);
lean_dec(x_7);
x_49 = lean_environment_add(x_22, x_24);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_49);
x_2 = x_6;
x_3 = x_50;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___redArg(x_1, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts_replayKernel(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_array_size(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
lean_inc(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Environment_replayConsts_replayKernel_spec__0(x_1, x_2, x_5, x_4, x_7, x_9, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___redArg(x_3, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Environment_replayConsts_replayKernel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Environment_replayConsts_replayKernel_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_Environment_replayConsts_replayKernel_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_List_forIn_x27_loop___at___Lean_Environment_replayConsts_replayKernel_spec__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts_replayKernel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Environment_replayConsts_replayKernel(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Environment_replayConsts_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Environment_0__Lean_AsyncConsts_add(x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(x_2, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l___private_Lean_Environment_0__Lean_AsyncConsts_add(x_2, x_8);
x_2 = x_13;
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_8);
x_3 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_6);
x_7 = l_Lean_Environment_replayConsts_replayKernel(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_7);
return x_6;
}
else
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Environment_0__Lean_EnvExtension_envExtensionsRef;
x_17 = lean_st_ref_get(x_16, x_5);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_nat_sub(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_nat_sub(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
lean_inc(x_23);
lean_inc(x_21);
x_26 = l_List_takeTR_go___redArg(x_21, x_21, x_20, x_23);
lean_dec(x_21);
lean_inc(x_25);
x_27 = l_List_takeTR_go___redArg(x_25, x_25, x_24, x_23);
lean_dec(x_25);
x_28 = l_List_reverse___redArg(x_26);
x_29 = lean_box(x_4);
lean_inc(x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Environment_replayConsts___lam__0___boxed), 6, 5);
lean_closure_set(x_30, 0, x_2);
lean_closure_set(x_30, 1, x_3);
lean_closure_set(x_30, 2, x_29);
lean_closure_set(x_30, 3, x_19);
lean_closure_set(x_30, 4, x_28);
x_31 = l_List_reverse___redArg(x_27);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_37 = lean_task_map(x_30, x_34, x_22, x_36);
x_38 = lean_ctor_get(x_1, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = l_List_foldl___at___Lean_Environment_replayConsts_spec__0(x_4, x_39, x_28);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_List_foldl___at___Lean_Environment_replayConsts_spec__0(x_4, x_41, x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_ctor_get(x_1, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 6);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 7);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_33);
lean_ctor_set(x_49, 2, x_37);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set(x_49, 4, x_44);
lean_ctor_set(x_49, 5, x_45);
lean_ctor_set(x_49, 6, x_46);
lean_ctor_set(x_49, 7, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*8, x_48);
lean_ctor_set(x_17, 0, x_49);
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_nat_sub(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_dec(x_7);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_mk_empty_array_with_capacity(x_54);
x_56 = lean_nat_sub(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_dec(x_12);
lean_inc(x_55);
lean_inc(x_53);
x_58 = l_List_takeTR_go___redArg(x_53, x_53, x_52, x_55);
lean_dec(x_53);
lean_inc(x_57);
x_59 = l_List_takeTR_go___redArg(x_57, x_57, x_56, x_55);
lean_dec(x_57);
x_60 = l_List_reverse___redArg(x_58);
x_61 = lean_box(x_4);
lean_inc(x_60);
x_62 = lean_alloc_closure((void*)(l_Lean_Environment_replayConsts___lam__0___boxed), 6, 5);
lean_closure_set(x_62, 0, x_2);
lean_closure_set(x_62, 1, x_3);
lean_closure_set(x_62, 2, x_61);
lean_closure_set(x_62, 3, x_50);
lean_closure_set(x_62, 4, x_60);
x_63 = l_List_reverse___redArg(x_59);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
x_67 = lean_box(0);
x_68 = lean_unbox(x_67);
x_69 = lean_task_map(x_62, x_66, x_54, x_68);
x_70 = lean_ctor_get(x_1, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = l_List_foldl___at___Lean_Environment_replayConsts_spec__0(x_4, x_71, x_60);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l_List_foldl___at___Lean_Environment_replayConsts_spec__0(x_4, x_73, x_63);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_ctor_get(x_1, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 6);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 7);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_81 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_81, 0, x_64);
lean_ctor_set(x_81, 1, x_65);
lean_ctor_set(x_81, 2, x_69);
lean_ctor_set(x_81, 3, x_75);
lean_ctor_set(x_81, 4, x_76);
lean_ctor_set(x_81, 5, x_77);
lean_ctor_set(x_81, 6, x_78);
lean_ctor_set(x_81, 7, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*8, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_51);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Environment_replayConsts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_List_foldl___at___Lean_Environment_replayConsts_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Environment_replayConsts___lam__0(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replayConsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Environment_replayConsts(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_Environment_find_x3f(x_1, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___Lean_Environment_dbgFormatAsyncState_spec__1___lam__0___boxed), 1, 0);
x_9 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_4, x_11, x_8);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("'", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = l_Lean_ConstantInfo_type(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_name_eq(x_19, x_3);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___redArg(x_3, x_4);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_3);
x_22 = lean_eval_const(x_1, x_2, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_1);
x_23 = l___private_Lean_Environment_0__Lean_Environment_throwUnexpectedType___redArg(x_3, x_4);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_evalConstCheck___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_evalConstCheck___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_evalConstCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_evalConstCheck(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_hasUnsafe___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Environment_findAsync_x3f(x_1, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_AsyncConstantInfo_isUnsafe(x_8);
return x_9;
}
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_hasUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Environment_hasUnsafe___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_find_expr(x_3, x_2);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_hasUnsafe___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_hasUnsafe___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_hasUnsafe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Environment_hasUnsafe(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst_unsafe__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_realizeConst_unsafe__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Environment_realizeConst_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_6, x_3);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Environment_realizeConst_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Lean_Environment_0__Lean_AsyncConsts_find_x3f(x_1, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l___private_Lean_Environment_0__Lean_AsyncConsts_add(x_1, x_3);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_5, 0, x_3);
x_6 = l_Lean_KVMap_insert(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_realizeConst_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_task_pure(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_ctor_get(x_5, 2);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_8 = x_20;
goto block_11;
}
else
{
lean_dec(x_12);
x_8 = x_5;
goto block_11;
}
block_11:
{
lean_object* x_9; 
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(1, 2, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_2 = x_6;
x_3 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Environment_realizeConst_spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_name_eq(x_1, x_5);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_3);
x_6 = lean_apply_1(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_io_promise_resolve(x_7, x_2, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___Lean_Environment_realizeConst_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_io_promise_new(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Environment_realizeConst___lam__2___boxed), 4, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_io_map_task(x_10, x_11, x_12, x_2, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_io_set_heartbeats(x_3, x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_inc(x_20);
x_26 = lean_alloc_closure((void*)(l_Lean_Environment_realizeConst___lam__0), 2, 1);
lean_closure_set(x_26, 0, x_20);
x_27 = l_List_foldl___at___Lean_Environment_realizeConst_spec__1(x_18, x_20);
x_28 = l_List_foldl___at___Lean_Environment_realizeConst_spec__1(x_21, x_22);
x_29 = lean_ctor_get(x_1, 7);
lean_inc(x_29);
x_30 = lean_box(1);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_27);
x_33 = lean_ctor_get(x_1, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 6);
lean_inc(x_35);
x_36 = lean_unbox(x_30);
x_37 = lean_task_map(x_26, x_29, x_12, x_36);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_15);
lean_ctor_set(x_39, 3, x_13);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_34);
lean_ctor_set(x_39, 6, x_35);
lean_ctor_set(x_39, 7, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*8, x_38);
x_40 = lean_io_promise_result_opt(x_8);
lean_dec(x_8);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
lean_dec(x_4);
lean_ctor_set(x_6, 1, x_41);
lean_ctor_set(x_6, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_6);
lean_ctor_set(x_23, 0, x_42);
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_dec(x_23);
lean_inc(x_20);
x_44 = lean_alloc_closure((void*)(l_Lean_Environment_realizeConst___lam__0), 2, 1);
lean_closure_set(x_44, 0, x_20);
x_45 = l_List_foldl___at___Lean_Environment_realizeConst_spec__1(x_18, x_20);
x_46 = l_List_foldl___at___Lean_Environment_realizeConst_spec__1(x_21, x_22);
x_47 = lean_ctor_get(x_1, 7);
lean_inc(x_47);
x_48 = lean_box(1);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_ctor_set(x_13, 1, x_46);
lean_ctor_set(x_13, 0, x_45);
x_51 = lean_ctor_get(x_1, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 6);
lean_inc(x_53);
x_54 = lean_unbox(x_48);
x_55 = lean_task_map(x_44, x_47, x_12, x_54);
x_56 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_15);
lean_ctor_set(x_57, 3, x_13);
lean_ctor_set(x_57, 4, x_51);
lean_ctor_set(x_57, 5, x_52);
lean_ctor_set(x_57, 6, x_53);
lean_ctor_set(x_57, 7, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*8, x_56);
x_58 = lean_io_promise_result_opt(x_8);
lean_dec(x_8);
x_59 = lean_ctor_get(x_4, 2);
lean_inc(x_59);
lean_dec(x_4);
lean_ctor_set(x_6, 1, x_59);
lean_ctor_set(x_6, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_6);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_43);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_62 = lean_ctor_get(x_13, 0);
x_63 = lean_ctor_get(x_13, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_13);
x_64 = lean_ctor_get(x_1, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_4, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_io_set_heartbeats(x_3, x_63);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
lean_inc(x_67);
x_73 = lean_alloc_closure((void*)(l_Lean_Environment_realizeConst___lam__0), 2, 1);
lean_closure_set(x_73, 0, x_67);
x_74 = l_List_foldl___at___Lean_Environment_realizeConst_spec__1(x_65, x_67);
x_75 = l_List_foldl___at___Lean_Environment_realizeConst_spec__1(x_68, x_69);
x_76 = lean_ctor_get(x_1, 7);
lean_inc(x_76);
x_77 = lean_box(1);
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_75);
x_81 = lean_ctor_get(x_1, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 6);
lean_inc(x_83);
x_84 = lean_unbox(x_77);
x_85 = lean_task_map(x_73, x_76, x_12, x_84);
x_86 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_87 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_62);
lean_ctor_set(x_87, 3, x_80);
lean_ctor_set(x_87, 4, x_81);
lean_ctor_set(x_87, 5, x_82);
lean_ctor_set(x_87, 6, x_83);
lean_ctor_set(x_87, 7, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*8, x_86);
x_88 = lean_io_promise_result_opt(x_8);
lean_dec(x_8);
x_89 = lean_ctor_get(x_4, 2);
lean_inc(x_89);
lean_dec(x_4);
lean_ctor_set(x_6, 1, x_89);
lean_ctor_set(x_6, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_6);
if (lean_is_scalar(x_72)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_72;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_71);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_92 = lean_ctor_get(x_6, 0);
x_93 = lean_ctor_get(x_6, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_6);
lean_inc(x_92);
lean_inc(x_4);
x_94 = lean_alloc_closure((void*)(l_Lean_Environment_realizeConst___lam__2___boxed), 4, 2);
lean_closure_set(x_94, 0, x_4);
lean_closure_set(x_94, 1, x_92);
x_95 = lean_ctor_get(x_1, 2);
lean_inc(x_95);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_io_map_task(x_94, x_95, x_96, x_2, x_93);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_1, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_4, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec(x_101);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_io_set_heartbeats(x_3, x_99);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
lean_inc(x_104);
x_110 = lean_alloc_closure((void*)(l_Lean_Environment_realizeConst___lam__0), 2, 1);
lean_closure_set(x_110, 0, x_104);
x_111 = l_List_foldl___at___Lean_Environment_realizeConst_spec__1(x_102, x_104);
x_112 = l_List_foldl___at___Lean_Environment_realizeConst_spec__1(x_105, x_106);
x_113 = lean_ctor_get(x_1, 7);
lean_inc(x_113);
x_114 = lean_box(1);
x_115 = lean_ctor_get(x_1, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_1, 1);
lean_inc(x_116);
if (lean_is_scalar(x_100)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_100;
}
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_112);
x_118 = lean_ctor_get(x_1, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 5);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 6);
lean_inc(x_120);
x_121 = lean_unbox(x_114);
x_122 = lean_task_map(x_110, x_113, x_96, x_121);
x_123 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
lean_dec(x_1);
x_124 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_124, 0, x_115);
lean_ctor_set(x_124, 1, x_116);
lean_ctor_set(x_124, 2, x_98);
lean_ctor_set(x_124, 3, x_117);
lean_ctor_set(x_124, 4, x_118);
lean_ctor_set(x_124, 5, x_119);
lean_ctor_set(x_124, 6, x_120);
lean_ctor_set(x_124, 7, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*8, x_123);
x_125 = lean_io_promise_result_opt(x_92);
lean_dec(x_92);
x_126 = lean_ctor_get(x_4, 2);
lean_inc(x_126);
lean_dec(x_4);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_127);
if (lean_is_scalar(x_109)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_109;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_108);
return x_129;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_119; lean_object* x_120; uint8_t x_166; lean_object* x_175; 
x_102 = lean_io_get_num_heartbeats(x_5);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_175 = lean_ctor_get(x_1, 4);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_box(0);
x_177 = lean_unbox(x_176);
x_166 = x_177;
goto block_174;
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_175);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_175, 0);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_3, x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_free_object(x_175);
x_166 = x_181;
goto block_174;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_183 = lean_mk_string_unchecked("Environment.realizeConst: cyclic realization of '", 49, 49);
x_184 = l_Lean_Name_toString(x_3, x_181, x_182);
x_185 = lean_string_append(x_183, x_184);
lean_dec(x_184);
x_186 = lean_mk_string_unchecked("'", 1, 1);
x_187 = lean_string_append(x_185, x_186);
lean_dec(x_186);
lean_ctor_set_tag(x_175, 18);
lean_ctor_set(x_175, 0, x_187);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_175);
lean_ctor_set(x_188, 1, x_104);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = lean_ctor_get(x_175, 0);
lean_inc(x_189);
lean_dec(x_175);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_3, x_190);
lean_dec(x_190);
if (x_191 == 0)
{
x_166 = x_191;
goto block_174;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_alloc_closure((void*)(l___private_Lean_Environment_0__Lean_AsyncConsts_add___lam__0___boxed), 1, 0);
x_193 = lean_mk_string_unchecked("Environment.realizeConst: cyclic realization of '", 49, 49);
x_194 = l_Lean_Name_toString(x_3, x_191, x_192);
x_195 = lean_string_append(x_193, x_194);
lean_dec(x_194);
x_196 = lean_mk_string_unchecked("'", 1, 1);
x_197 = lean_string_append(x_195, x_196);
lean_dec(x_196);
x_198 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_104);
return x_199;
}
}
}
block_11:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
block_101:
{
lean_object* x_19; 
x_19 = lean_st_ref_set(x_12, x_18, x_15);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 5);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_21, 6);
lean_inc(x_28);
lean_inc(x_14);
x_29 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_28, x_2, x_14);
x_30 = lean_ctor_get(x_21, 7);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*8);
lean_dec(x_21);
x_32 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_25);
lean_ctor_set(x_32, 4, x_26);
lean_ctor_set(x_32, 5, x_27);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set(x_32, 7, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*8, x_31);
x_33 = l___private_Lean_Environment_0__Lean_Environment_enterAsyncRealizing(x_3, x_32);
lean_dec(x_32);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = l_Lean_debug_skipKernelTC;
x_36 = lean_box(1);
x_37 = lean_unbox(x_36);
x_38 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_34, x_35, x_37);
lean_inc(x_33);
x_39 = lean_apply_3(x_4, x_33, x_38, x_20);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l___private_Lean_Environment_0__Lean_EnvExtension_envExtensionsRef;
x_56 = lean_st_ref_get(x_55, x_41);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_60 = lean_nat_sub(x_46, x_49);
lean_dec(x_49);
lean_dec(x_46);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
lean_dec(x_45);
x_62 = lean_mk_empty_array_with_capacity(x_50);
x_63 = lean_nat_sub(x_52, x_54);
lean_dec(x_54);
lean_dec(x_52);
x_64 = lean_ctor_get(x_51, 1);
lean_inc(x_64);
lean_dec(x_51);
lean_inc(x_62);
lean_inc(x_61);
x_65 = l_List_takeTR_go___redArg(x_61, x_61, x_60, x_62);
lean_dec(x_61);
lean_inc(x_64);
x_66 = l_List_takeTR_go___redArg(x_64, x_64, x_63, x_62);
lean_dec(x_64);
x_67 = l_List_reverse___redArg(x_65);
x_68 = lean_box(0);
x_69 = l_List_reverse___redArg(x_66);
lean_inc(x_42);
x_70 = l_List_mapTR_loop___at___Lean_Environment_realizeConst_spec__3(x_42, x_67, x_68);
lean_inc(x_42);
x_71 = l_List_mapTR_loop___at___Lean_Environment_realizeConst_spec__3(x_42, x_69, x_68);
lean_inc(x_70);
x_72 = lean_alloc_closure((void*)(l_Lean_Environment_replayConsts_replayKernel___boxed), 6, 5);
lean_closure_set(x_72, 0, x_33);
lean_closure_set(x_72, 1, x_42);
lean_closure_set(x_72, 2, x_36);
lean_closure_set(x_72, 3, x_58);
lean_closure_set(x_72, 4, x_70);
lean_ctor_set(x_56, 1, x_71);
lean_ctor_set(x_56, 0, x_70);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_56);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_43);
lean_inc(x_73);
x_74 = lean_io_promise_resolve(x_73, x_13, x_59);
lean_dec(x_13);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_apply_2(x_16, x_73, x_75);
x_6 = x_76;
goto block_11;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_77 = lean_ctor_get(x_56, 0);
x_78 = lean_ctor_get(x_56, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_56);
x_79 = lean_nat_sub(x_46, x_49);
lean_dec(x_49);
lean_dec(x_46);
x_80 = lean_ctor_get(x_45, 1);
lean_inc(x_80);
lean_dec(x_45);
x_81 = lean_mk_empty_array_with_capacity(x_50);
x_82 = lean_nat_sub(x_52, x_54);
lean_dec(x_54);
lean_dec(x_52);
x_83 = lean_ctor_get(x_51, 1);
lean_inc(x_83);
lean_dec(x_51);
lean_inc(x_81);
lean_inc(x_80);
x_84 = l_List_takeTR_go___redArg(x_80, x_80, x_79, x_81);
lean_dec(x_80);
lean_inc(x_83);
x_85 = l_List_takeTR_go___redArg(x_83, x_83, x_82, x_81);
lean_dec(x_83);
x_86 = l_List_reverse___redArg(x_84);
x_87 = lean_box(0);
x_88 = l_List_reverse___redArg(x_85);
lean_inc(x_42);
x_89 = l_List_mapTR_loop___at___Lean_Environment_realizeConst_spec__3(x_42, x_86, x_87);
lean_inc(x_42);
x_90 = l_List_mapTR_loop___at___Lean_Environment_realizeConst_spec__3(x_42, x_88, x_87);
lean_inc(x_89);
x_91 = lean_alloc_closure((void*)(l_Lean_Environment_replayConsts_replayKernel___boxed), 6, 5);
lean_closure_set(x_91, 0, x_33);
lean_closure_set(x_91, 1, x_42);
lean_closure_set(x_91, 2, x_36);
lean_closure_set(x_91, 3, x_77);
lean_closure_set(x_91, 4, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_43);
lean_inc(x_93);
x_94 = lean_io_promise_resolve(x_93, x_13, x_78);
lean_dec(x_13);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_apply_2(x_16, x_93, x_95);
x_6 = x_96;
goto block_11;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_19, 1);
lean_inc(x_97);
lean_dec(x_19);
x_98 = lean_ctor_get(x_17, 0);
lean_inc(x_98);
lean_dec(x_17);
x_99 = lean_task_get_own(x_98);
x_100 = lean_apply_2(x_16, x_99, x_97);
x_6 = x_100;
goto block_11;
}
}
block_118:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_io_promise_new(x_104);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_107, 2);
lean_inc(x_111);
x_112 = lean_st_ref_take(x_111, x_110);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_NameMap_find_x3f(lean_box(0), x_113, x_3);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_IO_Promise_result_x21___redArg(x_109);
lean_inc(x_3);
x_117 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_113, x_3, x_116);
x_12 = x_111;
x_13 = x_109;
x_14 = x_107;
x_15 = x_114;
x_16 = x_106;
x_17 = x_115;
x_18 = x_117;
goto block_101;
}
else
{
x_12 = x_111;
x_13 = x_109;
x_14 = x_107;
x_15 = x_114;
x_16 = x_106;
x_17 = x_115;
x_18 = x_113;
goto block_101;
}
}
block_165:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint64_t x_124; lean_object* x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; size_t x_133; size_t x_134; lean_object* x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; uint8_t x_140; 
x_121 = lean_ctor_get(x_120, 2);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_array_get_size(x_122);
x_124 = l_Lean_Name_hash___override(x_2);
x_125 = lean_unsigned_to_nat(32u);
x_126 = lean_uint64_of_nat(x_125);
x_127 = lean_uint64_shift_right(x_124, x_126);
x_128 = lean_uint64_xor(x_124, x_127);
x_129 = lean_unsigned_to_nat(16u);
x_130 = lean_uint64_of_nat(x_129);
x_131 = lean_uint64_shift_right(x_128, x_130);
x_132 = lean_uint64_xor(x_128, x_131);
x_133 = lean_uint64_to_usize(x_132);
x_134 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_usize_of_nat(x_135);
x_137 = lean_usize_sub(x_134, x_136);
x_138 = lean_usize_land(x_133, x_137);
x_139 = lean_array_uget(x_122, x_138);
lean_dec(x_122);
x_140 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_2, x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_1, 6);
lean_inc(x_141);
x_142 = l_Lean_NameMap_find_x3f(lean_box(0), x_141, x_2);
lean_dec(x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_119);
lean_dec(x_4);
lean_dec(x_1);
x_143 = lean_box(x_140);
x_144 = lean_alloc_closure((void*)(l_Lean_Environment_enableRealizationsForConst___lam__1___boxed), 2, 1);
lean_closure_set(x_144, 0, x_143);
x_145 = lean_mk_string_unchecked("trying to realize ", 18, 18);
x_146 = lean_box(1);
x_147 = lean_unbox(x_146);
lean_inc(x_144);
x_148 = l_Lean_Name_toString(x_3, x_147, x_144);
x_149 = lean_string_append(x_145, x_148);
lean_dec(x_148);
x_150 = lean_mk_string_unchecked(" but `enableRealizationsForConst` must be called for '", 54, 54);
x_151 = lean_string_append(x_149, x_150);
lean_dec(x_150);
x_152 = lean_unbox(x_146);
x_153 = l_Lean_Name_toString(x_2, x_152, x_144);
x_154 = lean_string_append(x_151, x_153);
lean_dec(x_153);
x_155 = lean_mk_string_unchecked("' first", 7, 7);
x_156 = lean_string_append(x_154, x_155);
lean_dec(x_155);
x_157 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_157, 0, x_156);
if (lean_is_scalar(x_105)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_105;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_104);
return x_158;
}
else
{
lean_object* x_159; 
lean_dec(x_105);
x_159 = lean_ctor_get(x_142, 0);
lean_inc(x_159);
lean_dec(x_142);
x_106 = x_119;
x_107 = x_159;
goto block_118;
}
}
else
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_1, 5);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_119);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_mk_string_unchecked("Environment.realizeConst: `realizedImportedConsts` is empty", 59, 59);
x_162 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_162, 0, x_161);
if (lean_is_scalar(x_105)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_105;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_104);
return x_163;
}
else
{
lean_object* x_164; 
lean_dec(x_105);
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
lean_dec(x_160);
x_106 = x_119;
x_107 = x_164;
goto block_118;
}
}
}
block_174:
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_box(x_166);
lean_inc(x_1);
x_168 = lean_alloc_closure((void*)(l_Lean_Environment_realizeConst___lam__1___boxed), 5, 3);
lean_closure_set(x_168, 0, x_1);
lean_closure_set(x_168, 1, x_167);
lean_closure_set(x_168, 2, x_103);
x_169 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_1, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec(x_170);
x_119 = x_168;
x_120 = x_171;
goto block_165;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_1, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_119 = x_168;
x_120 = x_173;
goto block_165;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Environment_realizeConst_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_realizeConst___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_realizeConst___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Environment_realizeConst___lam__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_isDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_kernel_is_def_eq(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Kernel_isDefEqGuarded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_kernel_is_def_eq(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_isDefEqGuarded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_Kernel_isDefEqGuarded(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_whnf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_kernel_whnf(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_kernel_check(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadEnvOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadEnvOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_setExporting(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__2(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Environment_setExporting(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Environment_setExporting(x_3, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__3___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_9);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_6, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l_Lean_Environment_header(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*5 + 4);
lean_dec(x_10);
x_12 = lean_box(x_1);
x_13 = lean_box(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__4___boxed), 7, 6);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_5);
lean_closure_set(x_16, 4, x_6);
lean_closure_set(x_16, 5, x_7);
x_17 = lean_apply_1(x_15, x_14);
x_18 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_box(x_1);
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__5___boxed), 9, 8);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_4);
lean_closure_set(x_14, 5, x_5);
lean_closure_set(x_14, 6, x_6);
lean_closure_set(x_14, 7, x_7);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__0___boxed), 1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(x_5);
lean_inc(x_8);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__6___boxed), 9, 8);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
lean_closure_set(x_12, 7, x_8);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__0___boxed), 1, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(x_8);
lean_inc(x_11);
lean_inc(x_10);
x_15 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__6___boxed), 9, 8);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_7);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_9);
lean_closure_set(x_15, 6, x_10);
lean_closure_set(x_15, 7, x_11);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_withExporting___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_withExporting___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_withExporting___redArg___lam__2(x_4, x_5, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withExporting___redArg___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withExporting___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_withExporting___redArg___lam__5(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_withExporting___redArg___lam__6(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_withExporting___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_withExporting(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_setExporting(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__4___boxed), 7, 6);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
x_12 = lean_apply_1(x_10, x_7);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_withoutExporting___redArg___lam__4___boxed), 9, 8);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_7);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_alloc_closure((void*)(l_Lean_withExporting___redArg___lam__0___boxed), 1, 0);
x_6 = lean_box(0);
x_7 = lean_alloc_closure((void*)(l_Lean_withoutExporting___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_withoutExporting___redArg___lam__0___boxed), 9, 8);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_8);
lean_closure_set(x_12, 7, x_9);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withoutExporting___redArg(x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_withoutExporting___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withoutExporting___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withoutExporting___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withoutExporting(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_15; uint8_t x_21; 
lean_inc(x_7);
x_21 = l_Lean_Environment_hasUnsafe(x_7, x_3);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Environment_hasUnsafe(x_7, x_4);
x_15 = x_22;
goto block_20;
}
else
{
lean_dec(x_7);
x_15 = x_21;
goto block_20;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_8);
x_13 = lean_apply_2(x_6, lean_box(0), x_12);
return x_13;
}
block_20:
{
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_8 = x_17;
goto block_14;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_8 = x_19;
goto block_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_mkDefinitionValInferrringUnsafe___redArg___lam__0), 7, 6);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_7);
lean_closure_set(x_12, 5, x_11);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkDefinitionValInferrringUnsafe___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT uint32_t l_Lean_getMaxHeight___lam__0(lean_object* x_1, lean_object* x_2, uint32_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
return x_3;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_9 = lean_box(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_task_get_own(x_10);
x_12 = l_Lean_ConstantInfo_hints(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 2)
{
uint32_t x_13; uint8_t x_14; 
x_13 = lean_ctor_get_uint32(x_12, 0);
lean_dec(x_12);
x_14 = lean_uint32_dec_lt(x_3, x_13);
if (x_14 == 0)
{
return x_3;
}
else
{
return x_13;
}
}
else
{
lean_dec(x_12);
return x_3;
}
}
else
{
lean_dec(x_9);
lean_dec(x_7);
return x_3;
}
}
}
}
LEAN_EXPORT uint32_t l_Lean_getMaxHeight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; 
x_3 = lean_alloc_closure((void*)(l_Lean_getMaxHeight___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_uint32_of_nat(x_4);
x_6 = lean_unsigned_to_nat(64u);
x_7 = l_Lean_mkPtrSet(lean_box(0), x_6);
x_8 = lean_unsigned_to_nat(8u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_shiftl(x_8, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box_uint32(x_5);
x_19 = l_Lean_Expr_FoldConstsImpl_fold_visit___redArg(x_3, x_2, x_18, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unbox_uint32(x_20);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_5 = l_Lean_getMaxHeight___lam__0(x_1, x_2, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Lean_getMaxHeight(x_1, x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
lean_object* initialize_Init_Control_StateRef(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_BinSearch(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Stream(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ImportingFlag(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_NameTrie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_SMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Setup(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Declaration(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LocalContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Profile(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_InstantiateLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrivateName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LoadDynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Dynamic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_StateRef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_BinSearch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Stream(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ImportingFlag(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameTrie(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_SMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Setup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_InstantiateLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrivateName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LoadDynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Dynamic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_Environment___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_debug_skipKernelTC = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_debug_skipKernelTC);
lean_dec_ref(res);
}l_Lean_EnvExtensionStateSpec = _init_l_Lean_EnvExtensionStateSpec();
lean_mark_persistent(l_Lean_EnvExtensionStateSpec);
l_Lean_instInhabitedEnvExtensionState = _init_l_Lean_instInhabitedEnvExtensionState();
lean_mark_persistent(l_Lean_instInhabitedEnvExtensionState);
l_Lean_instModuleIdxBEq = _init_l_Lean_instModuleIdxBEq();
lean_mark_persistent(l_Lean_instModuleIdxBEq);
l_Lean_instModuleIdxToString = _init_l_Lean_instModuleIdxToString();
lean_mark_persistent(l_Lean_instModuleIdxToString);
l_Lean_instInhabitedModuleIdx = _init_l_Lean_instInhabitedModuleIdx();
lean_mark_persistent(l_Lean_instInhabitedModuleIdx);
l_Lean_EnvExtensionEntrySpec = _init_l_Lean_EnvExtensionEntrySpec();
l_Lean_instInhabitedModuleData = _init_l_Lean_instInhabitedModuleData();
lean_mark_persistent(l_Lean_instInhabitedModuleData);
l_Lean_Kernel_instInhabitedDiagnostics = _init_l_Lean_Kernel_instInhabitedDiagnostics();
lean_mark_persistent(l_Lean_Kernel_instInhabitedDiagnostics);
l_Lean_instInhabitedConstantKind = _init_l_Lean_instInhabitedConstantKind();
l_Lean_instBEqConstantKind = _init_l_Lean_instBEqConstantKind();
lean_mark_persistent(l_Lean_instBEqConstantKind);
l_Lean_instReprConstantKind = _init_l_Lean_instReprConstantKind();
lean_mark_persistent(l_Lean_instReprConstantKind);
l_Lean_instInhabitedAsyncConstantInfo = _init_l_Lean_instInhabitedAsyncConstantInfo();
lean_mark_persistent(l_Lean_instInhabitedAsyncConstantInfo);
l_Lean_instInhabitedAsyncConsts = _init_l_Lean_instInhabitedAsyncConsts();
lean_mark_persistent(l_Lean_instInhabitedAsyncConsts);
l_Lean_instImpl____x40_Lean_Environment___hyg_1873_ = _init_l_Lean_instImpl____x40_Lean_Environment___hyg_1873_();
lean_mark_persistent(l_Lean_instImpl____x40_Lean_Environment___hyg_1873_);
l_Lean_instTypeNameAsyncConsts = _init_l_Lean_instTypeNameAsyncConsts();
lean_mark_persistent(l_Lean_instTypeNameAsyncConsts);
l_Lean_EnvExtension_instInhabitedAsyncMode = _init_l_Lean_EnvExtension_instInhabitedAsyncMode();
if (builtin) {res = l_Lean_EnvExtension_initFn____x40_Lean_Environment___hyg_6645_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Environment_0__Lean_EnvExtension_envExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Environment_0__Lean_EnvExtension_envExtensionsRef);
lean_dec_ref(res);
}l___private_Lean_Environment_0__Lean_EnvExtension_invalidExtMsg = _init_l___private_Lean_Environment_0__Lean_EnvExtension_invalidExtMsg();
lean_mark_persistent(l___private_Lean_Environment_0__Lean_EnvExtension_invalidExtMsg);
if (builtin) {res = l_Lean_initFn____x40_Lean_Environment___hyg_8540_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_persistentEnvExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_persistentEnvExtensionsRef);
lean_dec_ref(res);
}l_Lean_PersistentEnvExtensionDescr_name___autoParam = _init_l_Lean_PersistentEnvExtensionDescr_name___autoParam();
lean_mark_persistent(l_Lean_PersistentEnvExtensionDescr_name___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
