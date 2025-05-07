// Lean compiler output
// Module: Lake.Build.Library
// Imports: Lake.Build.Common Lake.Build.Targets
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_initFacetConfigs;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Target_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_modulesFacet;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__0(lean_object*, lean_object*);
lean_object* l_Lake_LeanLib_getModuleArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildDefaultFacets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Module_transImportsFacet;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_extraDepFacet;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildStaticLib(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__1(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mixArray(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lake_nullFormat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_leanArtsFacet;
extern lean_object* l_Lake_instDataKindUnit;
extern lean_object* l_Lake_Module_leanArtsFacet;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initLibraryFacetConfigs;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_extract(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildLean(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instMonad(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableRelPosLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7(uint8_t, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
extern lean_object* l_Lake_LeanLib_staticFacet;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_staticExportFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__1(uint8_t, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_OptDataKind_anonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_extraDepFacet;
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__1(uint8_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanLib_recBuildStatic___lam__2(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_mkRelPathString(lean_object*);
extern lean_object* l_Lake_Module_importsFacet;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig;
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nameToStaticLib(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_sharedFacet;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
lean_object* l_Lake_BuildInfo_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_4, x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_array_uget(x_2, x_4);
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_name_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
x_12 = x_30;
x_13 = x_10;
x_14 = x_11;
goto block_19;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_23, x_25, x_24, x_6, x_7, x_8, x_9, x_10, x_11);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_ctor_set(x_33, 1, x_37);
lean_ctor_set(x_33, 0, x_38);
x_12 = x_33;
x_13 = x_35;
x_14 = x_34;
goto block_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_12 = x_41;
x_13 = x_35;
x_14 = x_34;
goto block_19;
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_31, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_31, 0, x_47);
return x_31;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_ctor_get(x_32, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_51 = x_32;
} else {
 lean_dec_ref(x_32);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
}
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_5 = x_12;
x_10 = x_13;
x_11 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_box(0);
x_10 = lean_array_push(x_5, x_8);
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
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_5, 2);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_name_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Name_hash___override(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; lean_object* x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_array_get_size(x_1);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = l_Lean_Name_hash___override(x_30);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(32u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_unsigned_to_nat(16u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_usize_of_nat(x_42);
x_44 = lean_usize_sub(x_41, x_43);
x_45 = lean_usize_land(x_40, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_54; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; lean_object* x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; size_t x_124; size_t x_125; lean_object* x_126; size_t x_127; size_t x_128; size_t x_129; lean_object* x_130; uint8_t x_131; 
x_111 = lean_ctor_get(x_4, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_4, 1);
lean_inc(x_112);
x_113 = lean_array_get_size(x_112);
x_114 = lean_ctor_get(x_2, 2);
lean_inc(x_114);
x_115 = l_Lean_Name_hash___override(x_114);
lean_dec(x_114);
x_116 = lean_unsigned_to_nat(32u);
x_117 = lean_uint64_of_nat(x_116);
x_118 = lean_uint64_shift_right(x_115, x_117);
x_119 = lean_uint64_xor(x_115, x_118);
x_120 = lean_unsigned_to_nat(16u);
x_121 = lean_uint64_of_nat(x_120);
x_122 = lean_uint64_shift_right(x_119, x_121);
x_123 = lean_uint64_xor(x_119, x_122);
x_124 = lean_uint64_to_usize(x_123);
x_125 = lean_usize_of_nat(x_113);
lean_dec(x_113);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_usize_of_nat(x_126);
x_128 = lean_usize_sub(x_125, x_127);
x_129 = lean_usize_land(x_124, x_128);
x_130 = lean_array_uget(x_112, x_129);
x_131 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_2, x_130);
if (x_131 == 0)
{
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_4);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_133 = lean_ctor_get(x_4, 1);
lean_dec(x_133);
x_134 = lean_ctor_get(x_4, 0);
lean_dec(x_134);
x_135 = lean_box(0);
x_136 = lean_nat_add(x_111, x_126);
lean_dec(x_111);
lean_inc(x_2);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_2);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_137, 2, x_130);
x_138 = lean_array_uset(x_112, x_129, x_137);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_shiftl(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_138);
lean_ctor_set(x_4, 1, x_145);
lean_ctor_set(x_4, 0, x_136);
x_54 = x_4;
goto block_110;
}
else
{
lean_ctor_set(x_4, 1, x_138);
lean_ctor_set(x_4, 0, x_136);
x_54 = x_4;
goto block_110;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_dec(x_4);
x_146 = lean_box(0);
x_147 = lean_nat_add(x_111, x_126);
lean_dec(x_111);
lean_inc(x_2);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_2);
lean_ctor_set(x_148, 1, x_146);
lean_ctor_set(x_148, 2, x_130);
x_149 = lean_array_uset(x_112, x_129, x_148);
x_150 = lean_unsigned_to_nat(2u);
x_151 = lean_nat_shiftl(x_147, x_150);
x_152 = lean_unsigned_to_nat(3u);
x_153 = lean_nat_div(x_151, x_152);
lean_dec(x_151);
x_154 = lean_array_get_size(x_149);
x_155 = lean_nat_dec_le(x_153, x_154);
lean_dec(x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_149);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_156);
x_54 = x_157;
goto block_110;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_149);
x_54 = x_158;
goto block_110;
}
}
}
else
{
lean_dec(x_130);
lean_dec(x_112);
lean_dec(x_111);
x_54 = x_4;
goto block_110;
}
}
else
{
lean_dec(x_130);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = x_4;
x_12 = x_3;
x_13 = x_9;
x_14 = x_10;
goto block_18;
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
block_53:
{
lean_object* x_29; size_t x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_array_size(x_26);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_usize_of_nat(x_31);
x_33 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0(x_1, x_26, x_30, x_32, x_29, x_5, x_6, x_7, x_8, x_27, x_28);
lean_dec(x_26);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_array_push(x_39, x_2);
x_11 = x_38;
x_12 = x_40;
x_13 = x_37;
x_14 = x_36;
goto block_18;
}
else
{
uint8_t x_41; 
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_33, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_33, 0, x_46);
return x_33;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_dec(x_33);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_50 = x_34;
} else {
 lean_dec_ref(x_34);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
block_110:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = l_Lake_Module_importsFacet;
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lake_Module_keyword;
lean_inc(x_2);
x_59 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_2);
lean_ctor_set(x_59, 3, x_55);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_60 = lean_apply_6(x_5, x_59, x_6, x_7, x_8, x_9, x_10);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_io_wait(x_65, x_62);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get_size(x_71);
x_74 = lean_nat_dec_lt(x_72, x_73);
if (x_74 == 0)
{
lean_dec(x_73);
lean_dec(x_71);
x_25 = x_54;
x_26 = x_70;
x_27 = x_64;
x_28 = x_69;
goto block_53;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_73, x_73);
if (x_75 == 0)
{
lean_dec(x_73);
lean_dec(x_71);
x_25 = x_54;
x_26 = x_70;
x_27 = x_64;
x_28 = x_69;
goto block_53;
}
else
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_box(0);
x_77 = lean_usize_of_nat(x_72);
x_78 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_79 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_71, x_77, x_78, x_76, x_64, x_69);
lean_dec(x_71);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_25 = x_54;
x_26 = x_70;
x_27 = x_82;
x_28 = x_81;
goto block_53;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_54);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_66, 1);
lean_inc(x_84);
lean_dec(x_66);
x_85 = lean_ctor_get(x_67, 0);
lean_inc(x_85);
lean_dec(x_67);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_array_get_size(x_86);
x_89 = lean_nat_dec_lt(x_87, x_88);
if (x_89 == 0)
{
lean_dec(x_88);
lean_dec(x_86);
x_19 = x_85;
x_20 = x_64;
x_21 = x_84;
goto block_24;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_le(x_88, x_88);
if (x_90 == 0)
{
lean_dec(x_88);
lean_dec(x_86);
x_19 = x_85;
x_20 = x_64;
x_21 = x_84;
goto block_24;
}
else
{
lean_object* x_91; size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_box(0);
x_92 = lean_usize_of_nat(x_87);
x_93 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_94 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_86, x_92, x_93, x_91, x_64, x_84);
lean_dec(x_86);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_19 = x_85;
x_20 = x_97;
x_21 = x_96;
goto block_24;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_54);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_60);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_60, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_61);
if (x_100 == 0)
{
return x_60;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_61, 0);
x_102 = lean_ctor_get(x_61, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_61);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_60, 0, x_103);
return x_60;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_60, 1);
lean_inc(x_104);
lean_dec(x_60);
x_105 = lean_ctor_get(x_61, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_61, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_107 = x_61;
} else {
 lean_dec_ref(x_61);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_104);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_go_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lake_LeanLib_recCollectLocalModules_go(x_1, x_15, x_17, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_20, 0, x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_add(x_4, x_27);
x_4 = x_28;
x_5 = x_20;
x_10 = x_22;
x_11 = x_21;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_add(x_4, x_34);
x_4 = x_35;
x_5 = x_32;
x_10 = x_22;
x_11 = x_21;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_18, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_18, 0, x_42);
return x_18;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_46 = x_19;
} else {
 lean_dec_ref(x_19);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stderr(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stdout(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stdin(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_6(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg(x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_17 = l_ByteArray_empty;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_19);
x_20 = lean_st_mk_ref(x_19, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_mk_ref(x_19, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_IO_FS_Stream_ofBuffer(x_21);
lean_inc(x_24);
x_27 = l_IO_FS_Stream_ofBuffer(x_24);
x_28 = lean_box(x_2);
lean_inc(x_27);
x_29 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_27);
x_30 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2), 9, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_27);
lean_closure_set(x_30, 2, x_29);
x_31 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg(x_26, x_30, x_3, x_4, x_5, x_6, x_7, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_st_ref_get(x_24, x_33);
lean_dec(x_24);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_string_validate_utf8(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_39);
x_41 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
x_42 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
x_43 = lean_unsigned_to_nat(128u);
x_44 = lean_unsigned_to_nat(47u);
x_45 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
x_46 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
x_47 = l_panic___at___Lean_Name_getString_x21_spec__0(x_46);
x_9 = x_38;
x_10 = x_35;
x_11 = x_34;
x_12 = x_47;
goto block_16;
}
else
{
lean_object* x_48; 
x_48 = lean_string_from_utf8_unchecked(x_39);
lean_dec(x_39);
x_9 = x_38;
x_10 = x_35;
x_11 = x_34;
x_12 = x_48;
goto block_16;
}
}
else
{
uint8_t x_49; 
lean_dec(x_24);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_31, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_32);
if (x_51 == 0)
{
return x_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_32, 0);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_32);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_31, 0, x_54);
return x_31;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_dec(x_31);
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_58 = x_32;
} else {
 lean_dec_ref(x_32);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_15 = lean_array_get_size(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_90 = lean_string_utf8_byte_size(x_38);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_instDecidableEqPos(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_94 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_38, x_90, x_91);
x_95 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_38, x_94, x_90);
x_96 = lean_string_utf8_extract(x_38, x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_38);
x_97 = lean_string_append(x_93, x_96);
lean_dec(x_96);
x_98 = lean_box(1);
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
x_100 = lean_unbox(x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_100);
x_101 = lean_box(0);
x_102 = lean_array_push(x_37, x_99);
x_103 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(x_39, x_101, x_2, x_3, x_4, x_5, x_102, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_103;
goto block_89;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_38);
x_104 = lean_box(0);
x_105 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(x_39, x_104, x_2, x_3, x_4, x_5, x_37, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_105;
goto block_89;
}
block_89:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_array_get_size(x_45);
x_47 = l_Lake_instDecidableRelPosLt(x_15, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_free_object(x_41);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_15);
lean_dec(x_14);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_40, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_40, 0);
lean_dec(x_50);
lean_inc(x_45);
x_51 = l_Array_shrink___redArg(x_45, x_15);
x_52 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_8);
x_57 = lean_task_map(x_53, x_55, x_54, x_56);
x_58 = lean_ctor_get(x_44, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_ctor_set(x_41, 1, x_51);
lean_ctor_set(x_41, 0, x_60);
return x_40;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_40);
lean_inc(x_45);
x_61 = l_Array_shrink___redArg(x_45, x_15);
x_62 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_63 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0), 2, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_8);
x_67 = lean_task_map(x_63, x_65, x_64, x_66);
x_68 = lean_ctor_get(x_44, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_69);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_41);
lean_ctor_set(x_71, 1, x_42);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_41, 0);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_41);
x_74 = lean_array_get_size(x_73);
x_75 = l_Lake_instDecidableRelPosLt(x_15, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_15);
lean_dec(x_14);
return x_40;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_76 = x_40;
} else {
 lean_dec_ref(x_40);
 x_76 = lean_box(0);
}
lean_inc(x_73);
x_77 = l_Array_shrink___redArg(x_73, x_15);
x_78 = l_Array_extract(lean_box(0), x_73, x_15, x_74);
lean_dec(x_73);
x_79 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__0), 2, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_8);
x_83 = lean_task_map(x_79, x_81, x_80, x_82);
x_84 = lean_ctor_get(x_72, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_72, sizeof(void*)*3);
lean_dec(x_72);
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_14);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_42);
return x_88;
}
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
lean_dec(x_11);
x_16 = x_106;
x_17 = x_12;
goto block_35;
}
block_35:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract(lean_box(0), x_16, x_15, x_19);
lean_dec(x_16);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = lean_mk_string_unchecked("<nil>", 5, 5);
x_25 = l_Lake_BuildTrace_nil(x_24);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unbox(x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_task_pure(x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_31, 2, x_21);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_13;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lake_LeanLib_getModuleArray(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_array_size(x_13);
x_17 = lean_usize_of_nat(x_4);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0(x_1, x_13, x_16, x_17, x_15, x_6, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_13);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_mk_empty_array_with_capacity(x_4);
x_30 = lean_mk_string_unchecked("", 0, 0);
x_31 = lean_box(0);
x_32 = lean_mk_string_unchecked("<nil>", 5, 5);
x_33 = l_Lake_BuildTrace_nil(x_32);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_unbox(x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_35);
lean_ctor_set(x_19, 1, x_34);
lean_ctor_set(x_19, 0, x_27);
x_36 = lean_task_pure(x_19);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_5);
lean_ctor_set(x_38, 2, x_30);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_39);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_20, 0, x_38);
lean_ctor_set(x_18, 0, x_20);
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec(x_20);
x_41 = lean_mk_empty_array_with_capacity(x_4);
x_42 = lean_mk_string_unchecked("", 0, 0);
x_43 = lean_box(0);
x_44 = lean_mk_string_unchecked("<nil>", 5, 5);
x_45 = l_Lake_BuildTrace_nil(x_44);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_unbox(x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_47);
lean_ctor_set(x_19, 1, x_46);
lean_ctor_set(x_19, 0, x_40);
x_48 = lean_task_pure(x_19);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 2, x_42);
x_51 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_24);
lean_ctor_set(x_18, 0, x_52);
return x_18;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_55 = x_20;
} else {
 lean_dec_ref(x_20);
 x_55 = lean_box(0);
}
x_56 = lean_mk_empty_array_with_capacity(x_4);
x_57 = lean_mk_string_unchecked("", 0, 0);
x_58 = lean_box(0);
x_59 = lean_mk_string_unchecked("<nil>", 5, 5);
x_60 = l_Lake_BuildTrace_nil(x_59);
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_unbox(x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_task_pure(x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_5);
lean_ctor_set(x_66, 2, x_57);
x_67 = lean_unbox(x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_67);
if (lean_is_scalar(x_55)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_55;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_53);
lean_ctor_set(x_18, 0, x_68);
return x_18;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_dec(x_18);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_71 = x_19;
} else {
 lean_dec_ref(x_19);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_20, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_73 = x_20;
} else {
 lean_dec_ref(x_20);
 x_73 = lean_box(0);
}
x_74 = lean_mk_empty_array_with_capacity(x_4);
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = lean_box(0);
x_77 = lean_mk_string_unchecked("<nil>", 5, 5);
x_78 = l_Lake_BuildTrace_nil(x_77);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_unbox(x_76);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_80);
if (lean_is_scalar(x_71)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_71;
}
lean_ctor_set(x_81, 0, x_72);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_task_pure(x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_5);
lean_ctor_set(x_84, 2, x_75);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_85);
if (lean_is_scalar(x_73)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_73;
}
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_70);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_69);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_5);
x_88 = !lean_is_exclusive(x_18);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_18, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_19);
if (x_90 == 0)
{
return x_18;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_19, 0);
x_92 = lean_ctor_get(x_19, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_19);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_18, 0, x_93);
return x_18;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_18, 1);
lean_inc(x_94);
lean_dec(x_18);
x_95 = lean_ctor_get(x_19, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_19, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_97 = x_19;
} else {
 lean_dec_ref(x_19);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_12);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_12, 0);
x_102 = lean_io_error_to_string(x_101);
x_103 = lean_box(3);
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_unbox(x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_105);
x_106 = lean_array_get_size(x_10);
x_107 = lean_array_push(x_10, x_104);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_108);
return x_12;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_109 = lean_ctor_get(x_12, 0);
x_110 = lean_ctor_get(x_12, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_12);
x_111 = lean_io_error_to_string(x_109);
x_112 = lean_box(3);
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
x_114 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_114);
x_115 = lean_array_get_size(x_10);
x_116 = lean_array_push(x_10, x_113);
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
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftl(x_11, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 11, 5);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_10);
lean_closure_set(x_20, 3, x_9);
lean_closure_set(x_20, 4, x_8);
x_21 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1(x_20, x_2, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recCollectLocalModules_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_LeanLib_recCollectLocalModules___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_9, x_11, x_7);
x_13 = lean_string_append(x_4, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("\n", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_5 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0___boxed), 1, 0);
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Name_toString(x_9, x_4, x_5);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_8, x_2, x_11);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; uint8_t x_13; 
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_4, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_2);
x_5 = x_3;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_12, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_2);
x_5 = x_3;
goto block_11;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_4);
x_16 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_17 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(x_2, x_15, x_16, x_3);
lean_dec(x_2);
x_5 = x_17;
goto block_11;
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_string_utf8_byte_size(x_5);
lean_inc(x_7);
lean_inc(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_Substring_prevn(x_8, x_6, x_7);
lean_dec(x_8);
x_10 = lean_string_utf8_extract(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec(x_5);
return x_10;
}
}
else
{
size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_array_size(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
x_21 = l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(x_18, x_20, x_2);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Json_compress(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_modulesFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_modulesFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_3 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_alloc_closure((void*)(l_Lake_LeanLib_recCollectLocalModules), 7, 0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_1);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_LeanLib_modulesFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_modulesFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_modulesFacetConfig___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lake_Module_leanArtsFacet;
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lake_Module_keyword;
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = lean_apply_6(x_5, x_17, x_6, x_7, x_8, x_9, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lake_Job_mix___redArg(x_4, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_2, x_25);
x_2 = x_26;
x_4 = x_23;
x_9 = x_22;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_18, 0);
lean_dec(x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_9);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildLean(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = l_Lake_LeanLib_modulesFacet;
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_1);
lean_ctor_set(x_50, 3, x_43);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = lean_apply_6(x_2, x_50, x_3, x_4, x_5, x_6, x_7);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_io_wait(x_56, x_53);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_array_get_size(x_62);
x_65 = lean_nat_dec_lt(x_63, x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_62);
x_14 = x_61;
x_15 = x_55;
x_16 = x_60;
goto block_42;
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_64, x_64);
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec(x_62);
x_14 = x_61;
x_15 = x_55;
x_16 = x_60;
goto block_42;
}
else
{
lean_object* x_67; size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_box(0);
x_68 = lean_usize_of_nat(x_63);
x_69 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_70 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_62, x_68, x_69, x_67, x_55, x_60);
lean_dec(x_62);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_14 = x_61;
x_15 = x_73;
x_16 = x_72;
goto block_42;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_58, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
lean_dec(x_57);
x_76 = lean_ctor_get(x_58, 0);
lean_inc(x_76);
lean_dec(x_58);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_array_get_size(x_77);
x_80 = lean_nat_dec_lt(x_78, x_79);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_77);
x_8 = x_76;
x_9 = x_55;
x_10 = x_75;
goto block_13;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_79, x_79);
if (x_81 == 0)
{
lean_dec(x_79);
lean_dec(x_77);
x_8 = x_76;
x_9 = x_55;
x_10 = x_75;
goto block_13;
}
else
{
lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_box(0);
x_83 = lean_usize_of_nat(x_78);
x_84 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_85 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_77, x_83, x_84, x_82, x_55, x_75);
lean_dec(x_77);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_8 = x_76;
x_9 = x_88;
x_10 = x_87;
goto block_13;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_51);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_51, 0);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_52);
if (x_91 == 0)
{
return x_51;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_52, 0);
x_93 = lean_ctor_get(x_52, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_52);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_51, 0, x_94);
return x_51;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_51, 1);
lean_inc(x_95);
lean_dec(x_51);
x_96 = lean_ctor_get(x_52, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_52, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_98 = x_52;
} else {
 lean_dec_ref(x_52);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
return x_100;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
block_42:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_17 = lean_mk_string_unchecked("<nil>", 5, 5);
x_18 = lean_box(0);
x_19 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_22 = lean_box(0);
x_23 = l_Lake_BuildTrace_nil(x_17);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_task_pure(x_26);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_array_get_size(x_14);
x_33 = lean_nat_dec_lt(x_20, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_15);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_16);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_15);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_16);
return x_38;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = lean_usize_of_nat(x_20);
x_40 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_41 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0(x_14, x_39, x_40, x_30, x_2, x_3, x_4, x_5, x_15, x_16);
lean_dec(x_14);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildLean_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_1 = l_Lake_instDataKindUnit;
x_2 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildLean), 7, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_6, 0, lean_box(0));
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_array_push(x_3, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanLib_recBuildStatic___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_Target_fetchIn___redArg(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ModuleFacet_fetch___redArg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__3), 8, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(x_1);
x_16 = lean_apply_1(x_14, x_15);
x_17 = lean_array_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_2, x_11, x_17, x_19, x_16);
x_21 = lean_apply_6(x_20, x_5, x_6, x_7, x_8, x_9, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = l_Array_append(lean_box(0), x_3, x_26);
lean_dec(x_26);
lean_ctor_set(x_22, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l_Array_append(lean_box(0), x_3, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_35 = x_22;
} else {
 lean_dec_ref(x_22);
 x_35 = lean_box(0);
}
x_36 = l_Array_append(lean_box(0), x_3, x_33);
lean_dec(x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
else
{
lean_dec(x_22);
lean_dec(x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_9, 0);
lean_inc(x_126);
lean_dec(x_9);
x_127 = lean_io_wait(x_126, x_15);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_8);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_array_get_size(x_132);
x_135 = lean_nat_dec_lt(x_133, x_134);
if (x_135 == 0)
{
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_6);
x_97 = x_131;
x_98 = x_14;
x_99 = x_130;
goto block_125;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_134, x_134);
if (x_136 == 0)
{
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_6);
x_97 = x_131;
x_98 = x_14;
x_99 = x_130;
goto block_125;
}
else
{
lean_object* x_137; size_t x_138; size_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_box(0);
x_138 = lean_usize_of_nat(x_133);
x_139 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_140 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_7, x_132, x_138, x_139, x_137);
x_141 = lean_apply_2(x_140, x_14, x_130);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_97 = x_131;
x_98 = x_144;
x_99 = x_143;
goto block_125;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_131);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_dec(x_142);
x_33 = x_146;
x_34 = x_147;
x_35 = x_145;
goto block_38;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_128, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_127, 1);
lean_inc(x_149);
lean_dec(x_127);
x_150 = lean_ctor_get(x_128, 0);
lean_inc(x_150);
lean_dec(x_128);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_array_get_size(x_151);
x_154 = lean_nat_dec_lt(x_152, x_153);
if (x_154 == 0)
{
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_8);
lean_dec(x_6);
x_33 = x_150;
x_34 = x_14;
x_35 = x_149;
goto block_38;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_153, x_153);
if (x_155 == 0)
{
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_8);
lean_dec(x_6);
x_33 = x_150;
x_34 = x_14;
x_35 = x_149;
goto block_38;
}
else
{
lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_box(0);
x_157 = lean_usize_of_nat(x_152);
x_158 = lean_usize_of_nat(x_153);
lean_dec(x_153);
x_159 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_8, x_151, x_157, x_158, x_156);
x_160 = lean_apply_2(x_159, x_14, x_149);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_33 = x_150;
x_34 = x_163;
x_35 = x_162;
goto block_38;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_150);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_ctor_get(x_161, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_dec(x_161);
x_33 = x_165;
x_34 = x_166;
x_35 = x_164;
goto block_38;
}
}
}
}
block_32:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = l_Array_append(lean_box(0), x_18, x_17);
lean_dec(x_17);
x_22 = lean_mk_string_unchecked("<nil>", 5, 5);
x_23 = l_Lake_BuildTrace_nil(x_22);
x_24 = l_Lake_buildStaticLib(x_20, x_21, x_1, x_10, x_11, x_12, x_13, x_23, x_19);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_16);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
block_96:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 6);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_2, 2);
lean_inc(x_46);
lean_dec(x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 6);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Array_append(lean_box(0), x_45, x_48);
lean_dec(x_48);
x_50 = lean_array_size(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_usize_of_nat(x_51);
x_53 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_50, x_52, x_49);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_54 = lean_apply_6(x_53, x_10, x_11, x_12, x_13, x_40, x_41);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
if (x_1 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec(x_42);
x_60 = lean_ctor_get(x_43, 6);
lean_inc(x_60);
x_61 = l_System_FilePath_normalize(x_60);
x_62 = l_Lake_joinRelative(x_59, x_61);
lean_dec(x_61);
x_63 = lean_ctor_get(x_43, 8);
lean_inc(x_63);
lean_dec(x_43);
x_64 = l_System_FilePath_normalize(x_63);
x_65 = l_Lake_joinRelative(x_62, x_64);
lean_dec(x_64);
x_66 = lean_ctor_get(x_46, 4);
lean_inc(x_66);
lean_dec(x_46);
x_67 = l_Lake_nameToStaticLib(x_66);
x_68 = l_Lake_joinRelative(x_65, x_67);
lean_dec(x_67);
x_16 = x_58;
x_17 = x_57;
x_18 = x_39;
x_19 = x_56;
x_20 = x_68;
goto block_32;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
lean_dec(x_54);
x_70 = lean_ctor_get(x_55, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_55, 1);
lean_inc(x_71);
lean_dec(x_55);
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_dec(x_42);
x_73 = lean_ctor_get(x_43, 6);
lean_inc(x_73);
x_74 = l_System_FilePath_normalize(x_73);
x_75 = l_Lake_joinRelative(x_72, x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_43, 8);
lean_inc(x_76);
lean_dec(x_43);
x_77 = l_System_FilePath_normalize(x_76);
x_78 = l_Lake_joinRelative(x_75, x_77);
lean_dec(x_77);
x_79 = lean_ctor_get(x_46, 4);
lean_inc(x_79);
lean_dec(x_46);
x_80 = l_Lake_nameToStaticLib(x_79);
x_81 = lean_mk_string_unchecked("export", 6, 6);
x_82 = l_System_FilePath_addExtension(x_80, x_81);
lean_dec(x_81);
x_83 = l_Lake_joinRelative(x_78, x_82);
lean_dec(x_82);
x_16 = x_71;
x_17 = x_70;
x_18 = x_39;
x_19 = x_69;
x_20 = x_83;
goto block_32;
}
}
else
{
uint8_t x_84; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_84 = !lean_is_exclusive(x_54);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_54, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_55);
if (x_86 == 0)
{
return x_54;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_55, 0);
x_88 = lean_ctor_get(x_55, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_55);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_54, 0, x_89);
return x_54;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_54, 1);
lean_inc(x_90);
lean_dec(x_54);
x_91 = lean_ctor_get(x_55, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_55, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_93 = x_55;
} else {
 lean_dec_ref(x_55);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_90);
return x_95;
}
}
}
block_125:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = l_Array_empty(lean_box(0));
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_lt(x_101, x_102);
if (x_103 == 0)
{
lean_dec(x_102);
lean_dec(x_97);
lean_dec(x_5);
x_39 = x_100;
x_40 = x_98;
x_41 = x_99;
goto block_96;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_102, x_102);
if (x_104 == 0)
{
lean_dec(x_102);
lean_dec(x_97);
lean_dec(x_5);
x_39 = x_100;
x_40 = x_98;
x_41 = x_99;
goto block_96;
}
else
{
size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_usize_of_nat(x_101);
x_106 = lean_usize_of_nat(x_102);
lean_dec(x_102);
lean_inc(x_3);
x_107 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_5, x_97, x_105, x_106, x_100);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_108 = lean_apply_6(x_107, x_10, x_11, x_12, x_13, x_98, x_99);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_39 = x_111;
x_40 = x_112;
x_41 = x_110;
goto block_96;
}
else
{
uint8_t x_113; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_108, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_109);
if (x_115 == 0)
{
return x_108;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_109, 0);
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_109);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_108, 0, x_118);
return x_108;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_108, 1);
lean_inc(x_119);
lean_dec(x_108);
x_120 = lean_ctor_get(x_109, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_109, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_122 = x_109;
} else {
 lean_dec_ref(x_109);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_119);
return x_124;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_9 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__0___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 1, 0);
x_11 = l_instMonadEIO(lean_box(0));
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 8, 3);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
x_17 = l_Lake_EStateT_instFunctor___redArg(x_15);
x_18 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, lean_box(0));
lean_inc(x_12);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 7, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_12);
x_20 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
lean_inc(x_22);
x_23 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_22);
x_24 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_23);
lean_inc(x_24);
x_25 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 3);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, lean_box(0));
lean_closure_set(x_26, 2, x_24);
x_27 = l_Lake_instDataKindFilePath;
lean_inc(x_1);
x_94 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__1), 9, 2);
lean_closure_set(x_94, 0, x_1);
lean_closure_set(x_94, 1, x_27);
x_95 = l_Lake_EquipT_instMonad(lean_box(0), lean_box(0), x_25);
x_96 = lean_box(x_2);
lean_inc(x_95);
x_97 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__4___boxed), 10, 2);
lean_closure_set(x_97, 0, x_96);
lean_closure_set(x_97, 1, x_95);
x_98 = lean_ctor_get(x_6, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*1 + 3);
lean_dec(x_98);
x_100 = lean_box(2);
x_101 = lean_unbox(x_100);
x_102 = l_Lake_instDecidableEqVerbosity(x_99, x_101);
x_103 = lean_box(x_2);
lean_inc(x_9);
lean_inc(x_1);
x_104 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__5___boxed), 15, 8);
lean_closure_set(x_104, 0, x_103);
lean_closure_set(x_104, 1, x_1);
lean_closure_set(x_104, 2, x_95);
lean_closure_set(x_104, 3, x_94);
lean_closure_set(x_104, 4, x_97);
lean_closure_set(x_104, 5, x_22);
lean_closure_set(x_104, 6, x_9);
lean_closure_set(x_104, 7, x_9);
if (x_102 == 0)
{
lean_object* x_105; 
x_105 = lean_mk_string_unchecked("", 0, 0);
x_28 = x_104;
x_29 = x_105;
goto block_93;
}
else
{
if (x_2 == 0)
{
lean_object* x_106; 
x_106 = lean_mk_string_unchecked(" (without exports)", 18, 18);
x_28 = x_104;
x_29 = x_106;
goto block_93;
}
else
{
lean_object* x_107; 
x_107 = lean_mk_string_unchecked(" (with exports)", 15, 15);
x_28 = x_104;
x_29 = x_107;
goto block_93;
}
}
block_93:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_box(1);
x_32 = l_Lake_LeanLib_modulesFacet;
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_30);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_36 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_1);
lean_ctor_set(x_38, 3, x_32);
x_39 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch), 9, 3);
lean_closure_set(x_39, 0, lean_box(0));
lean_closure_set(x_39, 1, x_38);
lean_closure_set(x_39, 2, lean_box(0));
x_40 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_40, 0, lean_box(0));
lean_closure_set(x_40, 1, lean_box(0));
lean_closure_set(x_40, 2, x_26);
lean_closure_set(x_40, 3, lean_box(0));
lean_closure_set(x_40, 4, lean_box(0));
lean_closure_set(x_40, 5, x_39);
lean_closure_set(x_40, 6, x_28);
lean_inc(x_6);
x_41 = l_Lake_ensureJob(lean_box(0), x_27, x_40, x_3, x_4, x_5, x_6, x_7, x_8);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_unbox(x_31);
x_47 = l_Lean_Name_toString(x_30, x_46, x_10);
x_48 = lean_mk_string_unchecked(":static", 7, 7);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = lean_ctor_get(x_6, 3);
lean_inc(x_50);
lean_dec(x_6);
x_51 = lean_st_ref_take(x_50, x_43);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_string_append(x_49, x_29);
x_55 = lean_box(0);
x_56 = lean_ctor_get(x_45, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
lean_dec(x_45);
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_54);
x_59 = lean_unbox(x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_59);
x_60 = l_Lake_Job_toOpaque___redArg(x_58);
x_61 = lean_array_push(x_52, x_60);
x_62 = lean_st_ref_set(x_50, x_61, x_53);
lean_dec(x_50);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = l_Lake_Job_renew___redArg(x_58);
lean_ctor_set(x_42, 0, x_65);
lean_ctor_set(x_62, 0, x_42);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = l_Lake_Job_renew___redArg(x_58);
lean_ctor_set(x_42, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_69 = lean_ctor_get(x_42, 0);
x_70 = lean_ctor_get(x_42, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_42);
x_71 = lean_unbox(x_31);
x_72 = l_Lean_Name_toString(x_30, x_71, x_10);
x_73 = lean_mk_string_unchecked(":static", 7, 7);
x_74 = lean_string_append(x_72, x_73);
lean_dec(x_73);
x_75 = lean_ctor_get(x_6, 3);
lean_inc(x_75);
lean_dec(x_6);
x_76 = lean_st_ref_take(x_75, x_43);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_string_append(x_74, x_29);
x_80 = lean_box(0);
x_81 = lean_ctor_get(x_69, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
lean_dec(x_69);
x_83 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_79);
x_84 = lean_unbox(x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_84);
x_85 = l_Lake_Job_toOpaque___redArg(x_83);
x_86 = lean_array_push(x_77, x_85);
x_87 = lean_st_ref_set(x_75, x_86, x_78);
lean_dec(x_75);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = l_Lake_Job_renew___redArg(x_83);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_70);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_LeanLib_recBuildStatic___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_LeanLib_recBuildStatic___lam__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lake_LeanLib_recBuildStatic___lam__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l_Lake_LeanLib_recBuildStatic___lam__5(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_LeanLib_recBuildStatic(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
lean_inc_n(x_2, 2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = l_Lake_instDataKindFilePath;
x_21 = lean_name_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_43; 
lean_dec(x_18);
x_22 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 1, 0);
x_43 = l_Lean_Name_isAnonymous(x_19);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_box(x_43);
x_45 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_mk_string_unchecked("'", 1, 1);
x_47 = lean_unbox(x_9);
x_48 = l_Lean_Name_toString(x_19, x_47, x_45);
lean_inc(x_46);
x_49 = lean_string_append(x_46, x_48);
lean_dec(x_48);
x_50 = lean_string_append(x_49, x_46);
lean_dec(x_46);
x_23 = x_50;
goto block_42;
}
else
{
lean_object* x_51; 
lean_dec(x_19);
x_51 = lean_mk_string_unchecked("unknown", 7, 7);
x_23 = x_51;
goto block_42;
}
block_42:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_mk_string_unchecked("type mismtach in target '", 25, 25);
x_25 = l_Lake_PartialBuildKey_toString(x_2);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("': expected '", 13, 13);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_unbox(x_9);
x_30 = l_Lean_Name_toString(x_20, x_29, x_22);
x_31 = lean_string_append(x_28, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("', got ", 7, 7);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_33, x_23);
lean_dec(x_23);
x_35 = lean_box(3);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_array_get_size(x_16);
x_39 = lean_array_push(x_16, x_36);
if (lean_is_scalar(x_17)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_17;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_15)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_15;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_14);
return x_41;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_19);
lean_dec(x_2);
if (lean_is_scalar(x_17)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_17;
}
lean_ctor_set(x_52, 0, x_18);
lean_ctor_set(x_52, 1, x_16);
if (lean_is_scalar(x_15)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_15;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_14);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_11, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
return x_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_12, 0);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_12);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_11, 0, x_59);
return x_11;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_dec(x_11);
x_61 = lean_ctor_get(x_12, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_12, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_63 = x_12;
} else {
 lean_dec_ref(x_12);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_4, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l_Lake_ModuleFacet_fetch___redArg(x_14, x_1, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_4, x_3, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_21, x_3, x_18);
x_3 = x_24;
x_4 = x_25;
x_9 = x_19;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_15, 0, x_32);
return x_15;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_36 = x_16;
} else {
 lean_dec_ref(x_16);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0(x_15, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = lean_array_uset(x_4, x_3, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_26 = lean_array_uset(x_22, x_3, x_19);
x_3 = x_25;
x_4 = x_26;
x_9 = x_20;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_16, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_16, 0, x_33);
return x_16;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_37 = x_17;
} else {
 lean_dec_ref(x_17);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_eq(x_3, x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_array_uget(x_2, x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 8);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(x_1);
x_26 = lean_apply_1(x_24, x_25);
x_27 = lean_array_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_usize_of_nat(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_21, x_27, x_29, x_26, x_6, x_7, x_8, x_9, x_10, x_11);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Array_append(lean_box(0), x_5, x_33);
lean_dec(x_33);
x_12 = x_35;
x_13 = x_34;
x_14 = x_32;
goto block_19;
}
else
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_12 = x_38;
x_13 = x_39;
x_14 = x_37;
goto block_19;
}
else
{
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_30;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_12;
x_10 = x_13;
x_11 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_eq(x_3, x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_array_uget(x_2, x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 8);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(x_1);
x_26 = lean_apply_1(x_24, x_25);
x_27 = lean_array_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_usize_of_nat(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_21, x_27, x_29, x_26, x_6, x_7, x_8, x_9, x_10, x_11);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Array_append(lean_box(0), x_5, x_33);
lean_dec(x_33);
x_12 = x_35;
x_13 = x_34;
x_14 = x_32;
goto block_19;
}
else
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_12 = x_38;
x_13 = x_39;
x_14 = x_37;
goto block_19;
}
else
{
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_30;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_18 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3(x_1, x_2, x_17, x_4, x_12, x_6, x_7, x_8, x_9, x_13, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = l_Lake_instDataKindFilePath;
x_15 = lean_array_get_size(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_90 = lean_string_utf8_byte_size(x_38);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_instDecidableEqPos(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_94 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_38, x_90, x_91);
x_95 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_38, x_94, x_90);
x_96 = lean_string_utf8_extract(x_38, x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_38);
x_97 = lean_string_append(x_93, x_96);
lean_dec(x_96);
x_98 = lean_box(1);
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
x_100 = lean_unbox(x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_100);
x_101 = lean_box(0);
x_102 = lean_array_push(x_37, x_99);
x_103 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(x_39, x_101, x_2, x_3, x_4, x_5, x_102, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_103;
goto block_89;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_38);
x_104 = lean_box(0);
x_105 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(x_39, x_104, x_2, x_3, x_4, x_5, x_37, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_105;
goto block_89;
}
block_89:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_array_get_size(x_45);
x_47 = l_Lake_instDecidableRelPosLt(x_15, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_free_object(x_41);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_15);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_40, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_40, 0);
lean_dec(x_50);
lean_inc(x_45);
x_51 = l_Array_shrink___redArg(x_45, x_15);
x_52 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_8);
x_57 = lean_task_map(x_53, x_55, x_54, x_56);
x_58 = lean_ctor_get(x_44, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_ctor_set(x_41, 1, x_51);
lean_ctor_set(x_41, 0, x_60);
return x_40;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_40);
lean_inc(x_45);
x_61 = l_Array_shrink___redArg(x_45, x_15);
x_62 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_63 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_8);
x_67 = lean_task_map(x_63, x_65, x_64, x_66);
x_68 = lean_ctor_get(x_44, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_69);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_41);
lean_ctor_set(x_71, 1, x_42);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_41, 0);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_41);
x_74 = lean_array_get_size(x_73);
x_75 = l_Lake_instDecidableRelPosLt(x_15, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_15);
return x_40;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_76 = x_40;
} else {
 lean_dec_ref(x_40);
 x_76 = lean_box(0);
}
lean_inc(x_73);
x_77 = l_Array_shrink___redArg(x_73, x_15);
x_78 = l_Array_extract(lean_box(0), x_73, x_15, x_74);
lean_dec(x_73);
x_79 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__0), 2, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_8);
x_83 = lean_task_map(x_79, x_81, x_80, x_82);
x_84 = lean_ctor_get(x_72, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_72, sizeof(void*)*3);
lean_dec(x_72);
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_14);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_42);
return x_88;
}
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
lean_dec(x_11);
x_16 = x_106;
x_17 = x_12;
goto block_35;
}
block_35:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract(lean_box(0), x_16, x_15, x_19);
lean_dec(x_16);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = lean_mk_string_unchecked("<nil>", 5, 5);
x_25 = l_Lake_BuildTrace_nil(x_24);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unbox(x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_task_pure(x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_31, 2, x_21);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_13;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_118; lean_object* x_119; 
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_118 = lean_apply_6(x_5, x_2, x_6, x_7, x_8, x_9, x_10);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_io_wait(x_123, x_120);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_array_get_size(x_129);
x_132 = lean_nat_dec_lt(x_130, x_131);
if (x_132 == 0)
{
lean_dec(x_131);
lean_dec(x_129);
x_90 = x_128;
x_91 = x_122;
x_92 = x_127;
goto block_117;
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_le(x_131, x_131);
if (x_133 == 0)
{
lean_dec(x_131);
lean_dec(x_129);
x_90 = x_128;
x_91 = x_122;
x_92 = x_127;
goto block_117;
}
else
{
lean_object* x_134; size_t x_135; size_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_box(0);
x_135 = lean_usize_of_nat(x_130);
x_136 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_137 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_129, x_135, x_136, x_134, x_122, x_127);
lean_dec(x_129);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_90 = x_128;
x_91 = x_140;
x_92 = x_139;
goto block_117;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
lean_dec(x_124);
x_143 = lean_ctor_get(x_125, 0);
lean_inc(x_143);
lean_dec(x_125);
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_array_get_size(x_144);
x_147 = lean_nat_dec_lt(x_145, x_146);
if (x_147 == 0)
{
lean_dec(x_146);
lean_dec(x_144);
x_28 = x_143;
x_29 = x_122;
x_30 = x_142;
goto block_33;
}
else
{
uint8_t x_148; 
x_148 = lean_nat_dec_le(x_146, x_146);
if (x_148 == 0)
{
lean_dec(x_146);
lean_dec(x_144);
x_28 = x_143;
x_29 = x_122;
x_30 = x_142;
goto block_33;
}
else
{
lean_object* x_149; size_t x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_box(0);
x_150 = lean_usize_of_nat(x_145);
x_151 = lean_usize_of_nat(x_146);
lean_dec(x_146);
x_152 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_144, x_150, x_151, x_149, x_122, x_142);
lean_dec(x_144);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_28 = x_143;
x_29 = x_155;
x_30 = x_154;
goto block_33;
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = !lean_is_exclusive(x_118);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_118, 0);
lean_dec(x_157);
x_158 = !lean_is_exclusive(x_119);
if (x_158 == 0)
{
return x_118;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_119, 0);
x_160 = lean_ctor_get(x_119, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_119);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_118, 0, x_161);
return x_118;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_118, 1);
lean_inc(x_162);
lean_dec(x_118);
x_163 = lean_ctor_get(x_119, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_119, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_165 = x_119;
} else {
 lean_dec_ref(x_119);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_162);
return x_167;
}
}
block_27:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Array_append(lean_box(0), x_12, x_11);
lean_dec(x_11);
x_17 = lean_mk_string_unchecked("<nil>", 5, 5);
x_18 = l_Lake_BuildTrace_nil(x_17);
x_19 = l_Lake_buildStaticLib(x_15, x_16, x_1, x_5, x_6, x_7, x_8, x_18, x_13);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
block_89:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_3, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 6);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 6);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Array_append(lean_box(0), x_39, x_42);
lean_dec(x_42);
x_44 = lean_array_size(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_usize_of_nat(x_45);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_47 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2(x_4, x_44, x_46, x_43, x_5, x_6, x_7, x_8, x_35, x_36);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
if (x_1 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
lean_dec(x_3);
x_53 = lean_ctor_get(x_37, 6);
lean_inc(x_53);
x_54 = l_System_FilePath_normalize(x_53);
x_55 = l_Lake_joinRelative(x_52, x_54);
lean_dec(x_54);
x_56 = lean_ctor_get(x_37, 8);
lean_inc(x_56);
lean_dec(x_37);
x_57 = l_System_FilePath_normalize(x_56);
x_58 = l_Lake_joinRelative(x_55, x_57);
lean_dec(x_57);
x_59 = lean_ctor_get(x_40, 4);
lean_inc(x_59);
lean_dec(x_40);
x_60 = l_Lake_nameToStaticLib(x_59);
x_61 = l_Lake_joinRelative(x_58, x_60);
lean_dec(x_60);
x_11 = x_50;
x_12 = x_34;
x_13 = x_49;
x_14 = x_51;
x_15 = x_61;
goto block_27;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_ctor_get(x_48, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_dec(x_48);
x_65 = lean_ctor_get(x_3, 1);
lean_inc(x_65);
lean_dec(x_3);
x_66 = lean_ctor_get(x_37, 6);
lean_inc(x_66);
x_67 = l_System_FilePath_normalize(x_66);
x_68 = l_Lake_joinRelative(x_65, x_67);
lean_dec(x_67);
x_69 = lean_ctor_get(x_37, 8);
lean_inc(x_69);
lean_dec(x_37);
x_70 = l_System_FilePath_normalize(x_69);
x_71 = l_Lake_joinRelative(x_68, x_70);
lean_dec(x_70);
x_72 = lean_ctor_get(x_40, 4);
lean_inc(x_72);
lean_dec(x_40);
x_73 = l_Lake_nameToStaticLib(x_72);
x_74 = lean_mk_string_unchecked("export", 6, 6);
x_75 = l_System_FilePath_addExtension(x_73, x_74);
lean_dec(x_74);
x_76 = l_Lake_joinRelative(x_71, x_75);
lean_dec(x_75);
x_11 = x_63;
x_12 = x_34;
x_13 = x_62;
x_14 = x_64;
x_15 = x_76;
goto block_27;
}
}
else
{
uint8_t x_77; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_47);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_47, 0);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_48);
if (x_79 == 0)
{
return x_47;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_48, 0);
x_81 = lean_ctor_get(x_48, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_48);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_47, 0, x_82);
return x_47;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_47, 1);
lean_inc(x_83);
lean_dec(x_47);
x_84 = lean_ctor_get(x_48, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_48, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_86 = x_48;
} else {
 lean_dec_ref(x_48);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
return x_88;
}
}
}
block_117:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = l_Array_empty(lean_box(0));
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_lt(x_94, x_95);
if (x_96 == 0)
{
lean_dec(x_95);
lean_dec(x_90);
x_34 = x_93;
x_35 = x_91;
x_36 = x_92;
goto block_89;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_95, x_95);
if (x_97 == 0)
{
lean_dec(x_95);
lean_dec(x_90);
x_34 = x_93;
x_35 = x_91;
x_36 = x_92;
goto block_89;
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_usize_of_nat(x_94);
x_99 = lean_usize_of_nat(x_95);
lean_dec(x_95);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3(x_1, x_90, x_98, x_99, x_93, x_5, x_6, x_7, x_8, x_91, x_92);
lean_dec(x_90);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_34 = x_103;
x_35 = x_104;
x_36 = x_102;
goto block_89;
}
else
{
uint8_t x_105; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_100);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_100, 0);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_101);
if (x_107 == 0)
{
return x_100;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_101, 0);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_101);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_100, 0, x_110);
return x_100;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_dec(x_100);
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_114 = x_101;
} else {
 lean_dec_ref(x_101);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
return x_116;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; 
x_9 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 1, 0);
x_75 = lean_ctor_get(x_6, 0);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*1 + 3);
lean_dec(x_75);
x_77 = lean_box(2);
x_78 = lean_unbox(x_77);
x_79 = l_Lake_instDecidableEqVerbosity(x_76, x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_mk_string_unchecked("", 0, 0);
x_10 = x_80;
goto block_74;
}
else
{
if (x_3 == 0)
{
lean_object* x_81; 
x_81 = lean_mk_string_unchecked(" (without exports)", 18, 18);
x_10 = x_81;
goto block_74;
}
else
{
lean_object* x_82; 
x_82 = lean_mk_string_unchecked(" (with exports)", 15, 15);
x_10 = x_82;
goto block_74;
}
}
block_74:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_box(1);
x_13 = l_Lake_LeanLib_modulesFacet;
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_inc(x_11);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
x_17 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_18 = l_Lean_Name_mkStr1(x_17);
lean_inc(x_2);
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 3, x_13);
x_20 = lean_box(x_3);
x_21 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_14);
lean_closure_set(x_21, 3, x_2);
lean_inc(x_6);
x_22 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5(x_21, x_1, x_4, x_5, x_6, x_7, x_8);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_unbox(x_12);
x_28 = l_Lean_Name_toString(x_11, x_27, x_9);
x_29 = lean_mk_string_unchecked(":static", 7, 7);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_6, 3);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_st_ref_take(x_31, x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_string_append(x_30, x_10);
x_36 = lean_box(0);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_unbox(x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_40);
x_41 = l_Lake_Job_toOpaque___redArg(x_39);
x_42 = lean_array_push(x_33, x_41);
x_43 = lean_st_ref_set(x_31, x_42, x_34);
lean_dec(x_31);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_23, 0, x_46);
lean_ctor_set(x_43, 0, x_23);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_23, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_50 = lean_ctor_get(x_23, 0);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_23);
x_52 = lean_unbox(x_12);
x_53 = l_Lean_Name_toString(x_11, x_52, x_9);
x_54 = lean_mk_string_unchecked(":static", 7, 7);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_56 = lean_ctor_get(x_6, 3);
lean_inc(x_56);
lean_dec(x_6);
x_57 = lean_st_ref_take(x_56, x_24);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_string_append(x_55, x_10);
x_61 = lean_box(0);
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_dec(x_50);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_60);
x_65 = lean_unbox(x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_65);
x_66 = l_Lake_Job_toOpaque___redArg(x_64);
x_67 = lean_array_push(x_58, x_66);
x_68 = lean_st_ref_set(x_56, x_67, x_59);
lean_dec(x_56);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = l_Lake_Job_renew___redArg(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_51);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_mkRelPathString(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Json_compress(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___lam__0), 7, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___lam__1___boxed), 2, 0);
x_3 = l_Lake_instDataKindFilePath;
x_4 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_2);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3_spec__3(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__3(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__5___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___lam__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_LeanLib_staticFacetConfig_spec__7(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_staticFacetConfig___lam__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticExportFacetConfig___lam__0), 7, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_LeanLib_staticFacetConfig___lam__1___boxed), 2, 0);
x_3 = l_Lake_instDataKindFilePath;
x_4 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_2);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildShared_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
lean_inc_n(x_2, 2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = l_Lake_instDataKindDynlib;
x_21 = lean_name_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_43; 
lean_dec(x_18);
x_22 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 1, 0);
x_43 = l_Lean_Name_isAnonymous(x_19);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_box(x_43);
x_45 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_mk_string_unchecked("'", 1, 1);
x_47 = lean_unbox(x_9);
x_48 = l_Lean_Name_toString(x_19, x_47, x_45);
lean_inc(x_46);
x_49 = lean_string_append(x_46, x_48);
lean_dec(x_48);
x_50 = lean_string_append(x_49, x_46);
lean_dec(x_46);
x_23 = x_50;
goto block_42;
}
else
{
lean_object* x_51; 
lean_dec(x_19);
x_51 = lean_mk_string_unchecked("unknown", 7, 7);
x_23 = x_51;
goto block_42;
}
block_42:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_mk_string_unchecked("type mismtach in target '", 25, 25);
x_25 = l_Lake_PartialBuildKey_toString(x_2);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("': expected '", 13, 13);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_unbox(x_9);
x_30 = l_Lean_Name_toString(x_20, x_29, x_22);
x_31 = lean_string_append(x_28, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("', got ", 7, 7);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_33, x_23);
lean_dec(x_23);
x_35 = lean_box(3);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_array_get_size(x_16);
x_39 = lean_array_push(x_16, x_36);
if (lean_is_scalar(x_17)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_17;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_15)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_15;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_14);
return x_41;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_19);
lean_dec(x_2);
if (lean_is_scalar(x_17)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_17;
}
lean_ctor_set(x_52, 0, x_18);
lean_ctor_set(x_52, 1, x_16);
if (lean_is_scalar(x_15)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_15;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_14);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_11, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_12);
if (x_56 == 0)
{
return x_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_12, 0);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_12);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_11, 0, x_59);
return x_11;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_dec(x_11);
x_61 = lean_ctor_get(x_12, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_12, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_63 = x_12;
} else {
 lean_dec_ref(x_12);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = l_Lean_Name_hash___override(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(32u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_shift_right(x_16, x_18);
x_20 = lean_uint64_xor(x_16, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_sub(x_22, x_24);
x_26 = lean_usize_land(x_21, x_25);
x_27 = lean_array_uget(x_9, x_26);
lean_dec(x_9);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_2, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
x_31 = lean_array_get_size(x_30);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = lean_usize_sub(x_32, x_24);
x_34 = lean_usize_land(x_21, x_33);
x_35 = lean_array_uget(x_30, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(x_2, x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_38 = lean_ctor_get(x_8, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 0);
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = lean_nat_add(x_29, x_23);
lean_dec(x_29);
lean_inc(x_2);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_35);
x_43 = lean_array_uset(x_30, x_34, x_42);
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_shiftl(x_41, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_43);
lean_ctor_set(x_8, 1, x_50);
lean_ctor_set(x_8, 0, x_41);
x_3 = x_8;
goto block_7;
}
else
{
lean_ctor_set(x_8, 1, x_43);
lean_ctor_set(x_8, 0, x_41);
x_3 = x_8;
goto block_7;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_8);
x_51 = lean_box(0);
x_52 = lean_nat_add(x_29, x_23);
lean_dec(x_29);
lean_inc(x_2);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_35);
x_54 = lean_array_uset(x_30, x_34, x_53);
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_nat_shiftl(x_52, x_55);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_div(x_56, x_57);
lean_dec(x_56);
x_59 = lean_array_get_size(x_54);
x_60 = lean_nat_dec_le(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
x_3 = x_62;
goto block_7;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_54);
x_3 = x_63;
goto block_7;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
x_3 = x_8;
goto block_7;
}
}
else
{
lean_dec(x_8);
lean_dec(x_2);
return x_1;
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__1(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lake_ExternLib_dynlibFacet;
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lake_ExternLib_keyword;
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = lean_apply_6(x_5, x_19, x_6, x_7, x_8, x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_array_push(x_4, x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_add(x_2, x_27);
x_2 = x_28;
x_4 = x_25;
x_9 = x_24;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_20, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_39 = x_21;
} else {
 lean_dec_ref(x_21);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_9);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lake_ExternLib_keyword;
x_18 = lean_name_eq(x_15, x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_16);
x_21 = lean_array_push(x_5, x_20);
x_6 = x_21;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildShared_spec__0(x_14, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_push(x_5, x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_5 = x_20;
x_10 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_15, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_15, 0, x_30);
return x_15;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_34 = x_16;
} else {
 lean_dec_ref(x_16);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_10);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Array_empty(lean_box(0));
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_array_uget(x_1, x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = l_Lean_NameSet_contains(x_20, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_4, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 0);
lean_dec(x_28);
x_29 = l_Lake_LeanLib_sharedFacet;
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_24);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
x_33 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 3, x_29);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = lean_apply_6(x_5, x_35, x_6, x_7, x_8, x_9, x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_array_push(x_21, x_39);
x_42 = l_Lean_NameSet_insert(x_20, x_24);
lean_ctor_set(x_4, 1, x_41);
lean_ctor_set(x_4, 0, x_42);
x_11 = x_4;
x_12 = x_40;
x_13 = x_38;
goto block_18;
}
else
{
uint8_t x_43; 
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_36, 0, x_48);
return x_36;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_dec(x_36);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_4);
x_55 = l_Lake_LeanLib_sharedFacet;
x_56 = lean_ctor_get(x_23, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_24);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_24);
x_59 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_23);
lean_ctor_set(x_61, 3, x_55);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_62 = lean_apply_6(x_5, x_61, x_6, x_7, x_8, x_9, x_10);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_array_push(x_21, x_65);
x_68 = l_Lean_NameSet_insert(x_20, x_24);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_11 = x_69;
x_12 = x_66;
x_13 = x_64;
goto block_18;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_63, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
return x_76;
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
x_11 = x_4;
x_12 = x_9;
x_13 = x_10;
goto block_18;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_4);
lean_ctor_set(x_77, 1, x_9);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_10);
return x_78;
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_11;
x_9 = x_12;
x_10 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_26; 
x_26 = lean_usize_dec_eq(x_2, x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_array_uget(x_1, x_2);
x_28 = l_Lake_Module_transImportsFacet;
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lake_Module_keyword;
x_32 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = lean_apply_6(x_5, x_32, x_6, x_7, x_8, x_9, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_io_wait(x_38, x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_44);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
x_17 = x_43;
x_18 = x_37;
x_19 = x_42;
goto block_25;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
x_17 = x_43;
x_18 = x_37;
x_19 = x_42;
goto block_25;
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_box(0);
x_50 = lean_usize_of_nat(x_45);
x_51 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_52 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_44, x_50, x_51, x_49, x_37, x_42);
lean_dec(x_44);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_17 = x_43;
x_18 = x_55;
x_19 = x_54;
goto block_25;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get_size(x_59);
x_62 = lean_nat_dec_lt(x_60, x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_59);
x_11 = x_58;
x_12 = x_37;
x_13 = x_57;
goto block_16;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_61, x_61);
if (x_63 == 0)
{
lean_dec(x_61);
lean_dec(x_59);
x_11 = x_58;
x_12 = x_37;
x_13 = x_57;
goto block_16;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_box(0);
x_65 = lean_usize_of_nat(x_60);
x_66 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_67 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_59, x_65, x_66, x_64, x_37, x_57);
lean_dec(x_59);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_11 = x_58;
x_12 = x_70;
x_13 = x_69;
goto block_16;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_33);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_33, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_34);
if (x_73 == 0)
{
return x_33;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_34, 0);
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_34);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_33, 0, x_76);
return x_33;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_33, 1);
lean_inc(x_77);
lean_dec(x_33);
x_78 = lean_ctor_get(x_34, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_80 = x_34;
} else {
 lean_dec_ref(x_34);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_4);
lean_ctor_set(x_83, 1, x_9);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_10);
return x_84;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_25:
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(x_4, x_17);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_2, x_22);
x_2 = x_23;
x_4 = x_20;
x_9 = x_18;
x_10 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_26; 
x_26 = lean_usize_dec_eq(x_2, x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_array_uget(x_1, x_2);
x_28 = l_Lake_Module_transImportsFacet;
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lake_Module_keyword;
x_32 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = lean_apply_6(x_5, x_32, x_6, x_7, x_8, x_9, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_io_wait(x_38, x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_44);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
x_17 = x_43;
x_18 = x_37;
x_19 = x_42;
goto block_25;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
x_17 = x_43;
x_18 = x_37;
x_19 = x_42;
goto block_25;
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_box(0);
x_50 = lean_usize_of_nat(x_45);
x_51 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_52 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_44, x_50, x_51, x_49, x_37, x_42);
lean_dec(x_44);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_17 = x_43;
x_18 = x_55;
x_19 = x_54;
goto block_25;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
lean_dec(x_40);
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get_size(x_59);
x_62 = lean_nat_dec_lt(x_60, x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_59);
x_11 = x_58;
x_12 = x_37;
x_13 = x_57;
goto block_16;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_61, x_61);
if (x_63 == 0)
{
lean_dec(x_61);
lean_dec(x_59);
x_11 = x_58;
x_12 = x_37;
x_13 = x_57;
goto block_16;
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_box(0);
x_65 = lean_usize_of_nat(x_60);
x_66 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_67 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_59, x_65, x_66, x_64, x_37, x_57);
lean_dec(x_59);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_11 = x_58;
x_12 = x_70;
x_13 = x_69;
goto block_16;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_33);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_33, 0);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_34);
if (x_73 == 0)
{
return x_33;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_34, 0);
x_75 = lean_ctor_get(x_34, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_34);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_33, 0, x_76);
return x_33;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_33, 1);
lean_inc(x_77);
lean_dec(x_33);
x_78 = lean_ctor_get(x_34, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_80 = x_34;
} else {
 lean_dec_ref(x_34);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_4);
lean_ctor_set(x_83, 1, x_9);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_10);
return x_84;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_25:
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(x_4, x_17);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_2, x_22);
x_24 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9_spec__9(x_1, x_23, x_3, x_20, x_5, x_6, x_7, x_8, x_18, x_19);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lake_Target_fetchIn___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__0(x_14, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_push(x_5, x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_5 = x_20;
x_10 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_15, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_15, 0, x_30);
return x_15;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_34 = x_16;
} else {
 lean_dec_ref(x_16);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_10);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_array_uget(x_1, x_2);
x_21 = lean_box(1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 8);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_1(x_24, x_21);
x_26 = lean_array_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_usize_of_nat(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_20, x_26, x_28, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Array_append(lean_box(0), x_4, x_32);
lean_dec(x_32);
x_11 = x_34;
x_12 = x_33;
x_13 = x_31;
goto block_18;
}
else
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_4);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_11 = x_37;
x_12 = x_38;
x_13 = x_36;
goto block_18;
}
else
{
lean_dec(x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_11;
x_9 = x_12;
x_10 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_array_uget(x_1, x_2);
x_21 = lean_box(1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 8);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_1(x_24, x_21);
x_26 = lean_array_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_usize_of_nat(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildStatic___at___Lake_LeanLib_staticFacetConfig_spec__0_spec__1(x_20, x_26, x_28, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Array_append(lean_box(0), x_4, x_32);
lean_dec(x_32);
x_11 = x_34;
x_12 = x_33;
x_13 = x_31;
goto block_18;
}
else
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_4);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_11 = x_37;
x_12 = x_38;
x_13 = x_36;
goto block_18;
}
else
{
lean_dec(x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12_spec__12(x_1, x_16, x_3, x_11, x_5, x_6, x_7, x_8, x_12, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_LeanLib_recCollectLocalModules_spec__1_spec__1___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = l_Lake_instDataKindDynlib;
x_15 = lean_array_get_size(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_90 = lean_string_utf8_byte_size(x_38);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_instDecidableEqPos(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_94 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_38, x_90, x_91);
x_95 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_38, x_94, x_90);
x_96 = lean_string_utf8_extract(x_38, x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_38);
x_97 = lean_string_append(x_93, x_96);
lean_dec(x_96);
x_98 = lean_box(1);
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
x_100 = lean_unbox(x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_100);
x_101 = lean_box(0);
x_102 = lean_array_push(x_37, x_99);
x_103 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__1(x_39, x_101, x_2, x_3, x_4, x_5, x_102, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_103;
goto block_89;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_38);
x_104 = lean_box(0);
x_105 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__1(x_39, x_104, x_2, x_3, x_4, x_5, x_37, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_105;
goto block_89;
}
block_89:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_array_get_size(x_45);
x_47 = l_Lake_instDecidableRelPosLt(x_15, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_free_object(x_41);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_15);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_40, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_40, 0);
lean_dec(x_50);
lean_inc(x_45);
x_51 = l_Array_shrink___redArg(x_45, x_15);
x_52 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__0), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_8);
x_57 = lean_task_map(x_53, x_55, x_54, x_56);
x_58 = lean_ctor_get(x_44, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_ctor_set(x_41, 1, x_51);
lean_ctor_set(x_41, 0, x_60);
return x_40;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_40);
lean_inc(x_45);
x_61 = l_Array_shrink___redArg(x_45, x_15);
x_62 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_63 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__0), 2, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_8);
x_67 = lean_task_map(x_63, x_65, x_64, x_66);
x_68 = lean_ctor_get(x_44, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_69);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_41);
lean_ctor_set(x_71, 1, x_42);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_41, 0);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_41);
x_74 = lean_array_get_size(x_73);
x_75 = l_Lake_instDecidableRelPosLt(x_15, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_15);
return x_40;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_76 = x_40;
} else {
 lean_dec_ref(x_40);
 x_76 = lean_box(0);
}
lean_inc(x_73);
x_77 = l_Array_shrink___redArg(x_73, x_15);
x_78 = l_Array_extract(lean_box(0), x_73, x_15, x_74);
lean_dec(x_73);
x_79 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__0), 2, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_8);
x_83 = lean_task_map(x_79, x_81, x_80, x_82);
x_84 = lean_ctor_get(x_72, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_72, sizeof(void*)*3);
lean_dec(x_72);
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_14);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_42);
return x_88;
}
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
lean_dec(x_11);
x_16 = x_106;
x_17 = x_12;
goto block_35;
}
block_35:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract(lean_box(0), x_16, x_15, x_19);
lean_dec(x_16);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = lean_mk_string_unchecked("<nil>", 5, 5);
x_25 = l_Lake_BuildTrace_nil(x_24);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unbox(x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_task_pure(x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_31, 2, x_21);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_13;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_247; lean_object* x_248; 
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_247 = lean_apply_6(x_5, x_4, x_6, x_7, x_8, x_9, x_10);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
lean_dec(x_248);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_io_wait(x_252, x_249);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
x_257 = lean_ctor_get(x_254, 0);
lean_inc(x_257);
lean_dec(x_254);
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
lean_dec(x_255);
x_259 = lean_unsigned_to_nat(0u);
x_260 = lean_array_get_size(x_258);
x_261 = lean_nat_dec_lt(x_259, x_260);
if (x_261 == 0)
{
lean_dec(x_260);
lean_dec(x_258);
x_219 = x_257;
x_220 = x_251;
x_221 = x_256;
goto block_246;
}
else
{
uint8_t x_262; 
x_262 = lean_nat_dec_le(x_260, x_260);
if (x_262 == 0)
{
lean_dec(x_260);
lean_dec(x_258);
x_219 = x_257;
x_220 = x_251;
x_221 = x_256;
goto block_246;
}
else
{
lean_object* x_263; size_t x_264; size_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = lean_box(0);
x_264 = lean_usize_of_nat(x_259);
x_265 = lean_usize_of_nat(x_260);
lean_dec(x_260);
x_266 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_258, x_264, x_265, x_263, x_251, x_256);
lean_dec(x_258);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_219 = x_257;
x_220 = x_269;
x_221 = x_268;
goto block_246;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_ctor_get(x_254, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_253, 1);
lean_inc(x_271);
lean_dec(x_253);
x_272 = lean_ctor_get(x_254, 0);
lean_inc(x_272);
lean_dec(x_254);
x_273 = lean_ctor_get(x_270, 0);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_unsigned_to_nat(0u);
x_275 = lean_array_get_size(x_273);
x_276 = lean_nat_dec_lt(x_274, x_275);
if (x_276 == 0)
{
lean_dec(x_275);
lean_dec(x_273);
x_178 = x_272;
x_179 = x_251;
x_180 = x_271;
goto block_183;
}
else
{
uint8_t x_277; 
x_277 = lean_nat_dec_le(x_275, x_275);
if (x_277 == 0)
{
lean_dec(x_275);
lean_dec(x_273);
x_178 = x_272;
x_179 = x_251;
x_180 = x_271;
goto block_183;
}
else
{
lean_object* x_278; size_t x_279; size_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_278 = lean_box(0);
x_279 = lean_usize_of_nat(x_274);
x_280 = lean_usize_of_nat(x_275);
lean_dec(x_275);
x_281 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recCollectLocalModules_go_spec__1(x_273, x_279, x_280, x_278, x_251, x_271);
lean_dec(x_273);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_178 = x_272;
x_179 = x_284;
x_180 = x_283;
goto block_183;
}
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_247);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_247, 0);
lean_dec(x_286);
x_287 = !lean_is_exclusive(x_248);
if (x_287 == 0)
{
return x_247;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_248, 0);
x_289 = lean_ctor_get(x_248, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_248);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
lean_ctor_set(x_247, 0, x_290);
return x_247;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_291 = lean_ctor_get(x_247, 1);
lean_inc(x_291);
lean_dec(x_247);
x_292 = lean_ctor_get(x_248, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_248, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_294 = x_248;
} else {
 lean_dec_ref(x_248);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_291);
return x_296;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_56:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_25 = lean_ctor_get(x_17, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_21, 6);
lean_inc(x_27);
x_28 = l_System_FilePath_normalize(x_27);
x_29 = l_Lake_joinRelative(x_26, x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_21, 8);
lean_inc(x_30);
lean_dec(x_21);
x_31 = l_System_FilePath_normalize(x_30);
x_32 = l_Lake_joinRelative(x_29, x_31);
lean_dec(x_31);
lean_inc(x_25);
x_33 = l_Lake_nameToSharedLib(x_25);
x_34 = l_Lake_joinRelative(x_32, x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_18, 9);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 9);
lean_inc(x_36);
x_37 = l_Array_append(lean_box(0), x_35, x_36);
lean_dec(x_36);
x_38 = lean_ctor_get(x_18, 8);
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_ctor_get(x_20, 8);
lean_inc(x_39);
lean_dec(x_20);
x_40 = l_Array_append(lean_box(0), x_38, x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_17, 2);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_array_get_size(x_41);
lean_dec(x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_42);
x_45 = l_System_Platform_isWindows;
x_46 = lean_mk_string_unchecked("<nil>", 5, 5);
x_47 = l_Lake_BuildTrace_nil(x_46);
x_48 = l_Lake_buildLeanSharedLib(x_25, x_34, x_19, x_22, x_37, x_40, x_44, x_45, x_5, x_6, x_7, x_8, x_47, x_24);
lean_dec(x_19);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_23);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_23);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
block_80:
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_array_get_size(x_66);
x_68 = lean_nat_dec_lt(x_63, x_67);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
x_17 = x_57;
x_18 = x_58;
x_19 = x_60;
x_20 = x_59;
x_21 = x_64;
x_22 = x_62;
x_23 = x_61;
x_24 = x_65;
goto block_56;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_67, x_67);
if (x_69 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
x_17 = x_57;
x_18 = x_58;
x_19 = x_60;
x_20 = x_59;
x_21 = x_64;
x_22 = x_62;
x_23 = x_61;
x_24 = x_65;
goto block_56;
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_usize_of_nat(x_63);
x_71 = lean_usize_of_nat(x_67);
lean_dec(x_67);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_72 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4(x_66, x_70, x_71, x_62, x_5, x_6, x_7, x_8, x_61, x_65);
lean_dec(x_66);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_17 = x_57;
x_18 = x_58;
x_19 = x_60;
x_20 = x_59;
x_21 = x_64;
x_22 = x_75;
x_23 = x_76;
x_24 = x_74;
goto block_56;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
x_11 = x_78;
x_12 = x_79;
x_13 = x_77;
goto block_16;
}
}
}
}
block_98:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_mk_empty_array_with_capacity(x_86);
x_91 = lean_ctor_get(x_1, 10);
lean_inc(x_91);
x_92 = lean_array_get_size(x_91);
x_93 = lean_nat_dec_lt(x_86, x_92);
if (x_93 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_57 = x_81;
x_58 = x_82;
x_59 = x_84;
x_60 = x_83;
x_61 = x_88;
x_62 = x_87;
x_63 = x_86;
x_64 = x_85;
x_65 = x_89;
x_66 = x_90;
goto block_80;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_le(x_92, x_92);
if (x_94 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_57 = x_81;
x_58 = x_82;
x_59 = x_84;
x_60 = x_83;
x_61 = x_88;
x_62 = x_87;
x_63 = x_86;
x_64 = x_85;
x_65 = x_89;
x_66 = x_90;
goto block_80;
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; 
x_95 = lean_usize_of_nat(x_86);
x_96 = lean_usize_of_nat(x_92);
lean_dec(x_92);
x_97 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5(x_2, x_91, x_95, x_96, x_90);
lean_dec(x_91);
lean_dec(x_2);
x_57 = x_81;
x_58 = x_82;
x_59 = x_84;
x_60 = x_83;
x_61 = x_88;
x_62 = x_87;
x_63 = x_86;
x_64 = x_85;
x_65 = x_89;
x_66 = x_97;
goto block_80;
}
}
}
block_124:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_100, 7);
lean_inc(x_108);
x_109 = lean_ctor_get(x_102, 7);
lean_inc(x_109);
x_110 = l_Array_append(lean_box(0), x_108, x_109);
lean_dec(x_109);
x_111 = lean_array_get_size(x_110);
x_112 = lean_nat_dec_lt(x_103, x_111);
if (x_112 == 0)
{
lean_dec(x_111);
lean_dec(x_110);
x_81 = x_99;
x_82 = x_100;
x_83 = x_101;
x_84 = x_102;
x_85 = x_104;
x_86 = x_103;
x_87 = x_105;
x_88 = x_106;
x_89 = x_107;
goto block_98;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_111, x_111);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec(x_110);
x_81 = x_99;
x_82 = x_100;
x_83 = x_101;
x_84 = x_102;
x_85 = x_104;
x_86 = x_103;
x_87 = x_105;
x_88 = x_106;
x_89 = x_107;
goto block_98;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_usize_of_nat(x_103);
x_115 = lean_usize_of_nat(x_111);
lean_dec(x_111);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_116 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__6(x_2, x_110, x_114, x_115, x_105, x_5, x_6, x_7, x_8, x_106, x_107);
lean_dec(x_110);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_81 = x_99;
x_82 = x_100;
x_83 = x_101;
x_84 = x_102;
x_85 = x_104;
x_86 = x_103;
x_87 = x_119;
x_88 = x_120;
x_89 = x_118;
goto block_98;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
lean_dec(x_117);
x_11 = x_122;
x_12 = x_123;
x_13 = x_121;
goto block_16;
}
}
}
}
block_153:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_mk_empty_array_with_capacity(x_130);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_array_get_size(x_135);
x_137 = lean_nat_dec_lt(x_130, x_136);
if (x_137 == 0)
{
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_3);
x_99 = x_125;
x_100 = x_126;
x_101 = x_128;
x_102 = x_127;
x_103 = x_130;
x_104 = x_129;
x_105 = x_134;
x_106 = x_132;
x_107 = x_133;
goto block_124;
}
else
{
uint8_t x_138; 
x_138 = lean_nat_dec_le(x_136, x_136);
if (x_138 == 0)
{
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_3);
x_99 = x_125;
x_100 = x_126;
x_101 = x_128;
x_102 = x_127;
x_103 = x_130;
x_104 = x_129;
x_105 = x_134;
x_106 = x_132;
x_107 = x_133;
goto block_124;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_box(0);
x_140 = l_Lean_NameSet_insert(x_139, x_3);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_134);
x_142 = lean_usize_of_nat(x_130);
x_143 = lean_usize_of_nat(x_136);
lean_dec(x_136);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_144 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8(x_135, x_142, x_143, x_141, x_5, x_6, x_7, x_8, x_132, x_133);
lean_dec(x_135);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_99 = x_125;
x_100 = x_126;
x_101 = x_128;
x_102 = x_127;
x_103 = x_130;
x_104 = x_129;
x_105 = x_149;
x_106 = x_148;
x_107 = x_147;
goto block_124;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_dec(x_144);
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_dec(x_145);
x_11 = x_151;
x_12 = x_152;
x_13 = x_150;
goto block_16;
}
}
}
}
block_177:
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__7;
x_164 = lean_array_get_size(x_157);
x_165 = lean_nat_dec_lt(x_159, x_164);
if (x_165 == 0)
{
lean_dec(x_164);
lean_dec(x_157);
x_125 = x_154;
x_126 = x_155;
x_127 = x_156;
x_128 = x_160;
x_129 = x_158;
x_130 = x_159;
x_131 = x_163;
x_132 = x_161;
x_133 = x_162;
goto block_153;
}
else
{
uint8_t x_166; 
x_166 = lean_nat_dec_le(x_164, x_164);
if (x_166 == 0)
{
lean_dec(x_164);
lean_dec(x_157);
x_125 = x_154;
x_126 = x_155;
x_127 = x_156;
x_128 = x_160;
x_129 = x_158;
x_130 = x_159;
x_131 = x_163;
x_132 = x_161;
x_133 = x_162;
goto block_153;
}
else
{
size_t x_167; size_t x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_usize_of_nat(x_159);
x_168 = lean_usize_of_nat(x_164);
lean_dec(x_164);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_169 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9(x_157, x_167, x_168, x_163, x_5, x_6, x_7, x_8, x_161, x_162);
lean_dec(x_157);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_125 = x_154;
x_126 = x_155;
x_127 = x_156;
x_128 = x_160;
x_129 = x_158;
x_130 = x_159;
x_131 = x_172;
x_132 = x_173;
x_133 = x_171;
goto block_153;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
lean_dec(x_169);
x_175 = lean_ctor_get(x_170, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_170, 1);
lean_inc(x_176);
lean_dec(x_170);
x_11 = x_175;
x_12 = x_176;
x_13 = x_174;
goto block_16;
}
}
}
}
block_183:
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
block_218:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_188 = lean_ctor_get(x_1, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_189, 6);
lean_inc(x_190);
x_191 = lean_ctor_get(x_2, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 6);
lean_inc(x_193);
x_194 = l_Array_append(lean_box(0), x_190, x_193);
lean_dec(x_193);
x_195 = lean_unsigned_to_nat(0u);
x_196 = lean_array_get_size(x_194);
x_197 = lean_nat_dec_lt(x_195, x_196);
if (x_197 == 0)
{
lean_dec(x_196);
lean_dec(x_194);
x_154 = x_191;
x_155 = x_189;
x_156 = x_192;
x_157 = x_184;
x_158 = x_188;
x_159 = x_195;
x_160 = x_185;
x_161 = x_186;
x_162 = x_187;
goto block_177;
}
else
{
uint8_t x_198; 
x_198 = lean_nat_dec_le(x_196, x_196);
if (x_198 == 0)
{
lean_dec(x_196);
lean_dec(x_194);
x_154 = x_191;
x_155 = x_189;
x_156 = x_192;
x_157 = x_184;
x_158 = x_188;
x_159 = x_195;
x_160 = x_185;
x_161 = x_186;
x_162 = x_187;
goto block_177;
}
else
{
size_t x_199; size_t x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_usize_of_nat(x_195);
x_200 = lean_usize_of_nat(x_196);
lean_dec(x_196);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_201 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11(x_2, x_194, x_199, x_200, x_185, x_5, x_6, x_7, x_8, x_186, x_187);
lean_dec(x_194);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_154 = x_191;
x_155 = x_189;
x_156 = x_192;
x_157 = x_184;
x_158 = x_188;
x_159 = x_195;
x_160 = x_204;
x_161 = x_205;
x_162 = x_203;
goto block_177;
}
else
{
uint8_t x_206; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = !lean_is_exclusive(x_201);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_201, 0);
lean_dec(x_207);
x_208 = !lean_is_exclusive(x_202);
if (x_208 == 0)
{
return x_201;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_202, 0);
x_210 = lean_ctor_get(x_202, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_202);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_201, 0, x_211);
return x_201;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_201, 1);
lean_inc(x_212);
lean_dec(x_201);
x_213 = lean_ctor_get(x_202, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_202, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_215 = x_202;
} else {
 lean_dec_ref(x_202);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_212);
return x_217;
}
}
}
}
}
block_246:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_222 = l_Array_empty(lean_box(0));
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_array_get_size(x_219);
x_225 = lean_nat_dec_lt(x_223, x_224);
if (x_225 == 0)
{
lean_dec(x_224);
x_184 = x_219;
x_185 = x_222;
x_186 = x_220;
x_187 = x_221;
goto block_218;
}
else
{
uint8_t x_226; 
x_226 = lean_nat_dec_le(x_224, x_224);
if (x_226 == 0)
{
lean_dec(x_224);
x_184 = x_219;
x_185 = x_222;
x_186 = x_220;
x_187 = x_221;
goto block_218;
}
else
{
size_t x_227; size_t x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_usize_of_nat(x_223);
x_228 = lean_usize_of_nat(x_224);
lean_dec(x_224);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_229 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12(x_219, x_227, x_228, x_222, x_5, x_6, x_7, x_8, x_220, x_221);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_184 = x_219;
x_185 = x_232;
x_186 = x_233;
x_187 = x_231;
goto block_218;
}
else
{
uint8_t x_234; 
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_229);
if (x_234 == 0)
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_ctor_get(x_229, 0);
lean_dec(x_235);
x_236 = !lean_is_exclusive(x_230);
if (x_236 == 0)
{
return x_229;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_230, 0);
x_238 = lean_ctor_get(x_230, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_230);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set(x_229, 0, x_239);
return x_229;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_229, 1);
lean_inc(x_240);
lean_dec(x_229);
x_241 = lean_ctor_get(x_230, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_230, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_243 = x_230;
} else {
 lean_dec_ref(x_230);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_240);
return x_245;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lake_LeanLib_modulesFacet;
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_inc(x_8);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_14 = l_Lean_Name_mkStr1(x_13);
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_9);
lean_inc(x_8);
x_16 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildShared___lam__0), 10, 4);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_8);
lean_closure_set(x_16, 3, x_15);
lean_inc(x_5);
x_17 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14(x_16, x_2, x_3, x_4, x_5, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 1, 0);
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Name_toString(x_8, x_24, x_22);
x_26 = lean_mk_string_unchecked(":shared", 7, 7);
x_27 = lean_ctor_get(x_5, 3);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_st_ref_take(x_27, x_19);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_31);
x_36 = lean_unbox(x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_36);
x_37 = l_Lake_Job_toOpaque___redArg(x_35);
x_38 = lean_array_push(x_29, x_37);
x_39 = lean_st_ref_set(x_27, x_38, x_30);
lean_dec(x_27);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Lake_Job_renew___redArg(x_35);
lean_ctor_set(x_18, 0, x_42);
lean_ctor_set(x_39, 0, x_18);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lake_Job_renew___redArg(x_35);
lean_ctor_set(x_18, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_46 = lean_ctor_get(x_18, 0);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_18);
x_48 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 1, 0);
x_49 = lean_box(1);
x_50 = lean_unbox(x_49);
x_51 = l_Lean_Name_toString(x_8, x_50, x_48);
x_52 = lean_mk_string_unchecked(":shared", 7, 7);
x_53 = lean_ctor_get(x_5, 3);
lean_inc(x_53);
lean_dec(x_5);
x_54 = lean_st_ref_take(x_53, x_19);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_58 = lean_box(0);
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_dec(x_46);
x_61 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_57);
x_62 = lean_unbox(x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_62);
x_63 = l_Lake_Job_toOpaque___redArg(x_61);
x_64 = lean_array_push(x_55, x_63);
x_65 = lean_st_ref_set(x_53, x_64, x_56);
lean_dec(x_53);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = l_Lake_Job_renew___redArg(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_47);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_OrdHashSet_appendArray___at___Lake_LeanLib_recBuildShared_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__4(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__6(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__8(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9_spec__9(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__9(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__11(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12_spec__12(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_LeanLib_recBuildShared_spec__12(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_LeanLib_recBuildShared_spec__14___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Json_compress(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLib_sharedFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_instDataKindDynlib;
x_3 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildShared), 7, 0);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_1);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_LeanLib_sharedFacetConfig_spec__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanLib_sharedFacetConfig___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lake_Package_fetchTargetJob(x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lake_Job_mix___redArg(x_5, x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_5 = x_22;
x_10 = x_21;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_17, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_17, 0, x_32);
return x_17;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_36 = x_18;
} else {
 lean_dec_ref(x_18);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_17 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_15, x_16, x_16, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lake_Job_toOpaque___redArg(x_22);
lean_dec(x_22);
x_24 = l_Lake_Job_mix___redArg(x_5, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_24;
x_10 = x_21;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_17, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_17, 0, x_34);
return x_17;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_38 = x_18;
} else {
 lean_dec_ref(x_18);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_8 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildStatic___lam__2___boxed), 1, 0);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_8);
lean_inc(x_10);
x_13 = l_Lean_Name_toString(x_10, x_12, x_8);
x_14 = lean_mk_string_unchecked("/", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_8);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(":extraDep", 9, 9);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_box(0);
x_26 = l_Lake_BuildTrace_nil(x_21);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_unbox(x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_28);
x_29 = l_Lake_Package_extraDepFacet;
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_10);
x_31 = l_Lake_Package_keyword;
x_32 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_9);
lean_ctor_set(x_32, 3, x_29);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = lean_apply_6(x_2, x_32, x_3, x_4, x_5, x_6, x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 0, x_22);
x_39 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_40 = lean_task_pure(x_34);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_41);
x_44 = lean_unbox(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_44);
x_45 = l_Lake_Job_mix___redArg(x_43, x_37);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 6);
lean_inc(x_47);
x_48 = lean_array_size(x_47);
x_49 = lean_usize_of_nat(x_23);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(x_1, x_47, x_48, x_49, x_45, x_2, x_3, x_4, x_5, x_38, x_35);
lean_dec(x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_46, 5);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_array_size(x_55);
x_57 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(x_1, x_55, x_56, x_49, x_53, x_2, x_3, x_4, x_5, x_54, x_52);
lean_dec(x_55);
return x_57;
}
else
{
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; 
x_58 = lean_ctor_get(x_34, 0);
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_34);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_22);
lean_ctor_set(x_60, 1, x_27);
x_61 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_62 = lean_task_pure(x_60);
x_63 = lean_mk_string_unchecked("", 0, 0);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_63);
x_66 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_66);
x_67 = l_Lake_Job_mix___redArg(x_65, x_58);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 6);
lean_inc(x_69);
x_70 = lean_array_size(x_69);
x_71 = lean_usize_of_nat(x_23);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_72 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(x_1, x_69, x_70, x_71, x_67, x_2, x_3, x_4, x_5, x_59, x_35);
lean_dec(x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_ctor_get(x_68, 5);
lean_inc(x_77);
lean_dec(x_68);
x_78 = lean_array_size(x_77);
x_79 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(x_1, x_77, x_78, x_71, x_75, x_2, x_3, x_4, x_5, x_76, x_74);
lean_dec(x_77);
return x_79;
}
else
{
lean_dec(x_73);
lean_dec(x_68);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_72;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_33);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_33, 0);
lean_dec(x_81);
return x_33;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_33, 1);
lean_inc(x_82);
lean_dec(x_33);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_34);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_LeanLib_recBuildExtraDepTargets_spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_1 = l_Lake_instDataKindUnit;
x_2 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildExtraDepTargets), 7, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_6, 0, lean_box(0));
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_box(0);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_21 = l_Lean_Name_mkStr1(x_20);
lean_inc(x_1);
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_1);
lean_ctor_set(x_22, 3, x_14);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = lean_apply_6(x_5, x_22, x_6, x_7, x_8, x_9, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_array_uset(x_4, x_3, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = l_Lake_Job_toOpaque___redArg(x_36);
lean_dec(x_36);
x_27 = x_38;
x_28 = x_37;
x_29 = x_25;
goto block_35;
}
else
{
lean_object* x_39; 
lean_dec(x_25);
lean_dec(x_24);
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_dec(x_23);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_27 = x_41;
x_28 = x_42;
x_29 = x_40;
goto block_35;
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_23);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_23, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_23;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_23, 0, x_48);
return x_23;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_23, 1);
lean_inc(x_49);
lean_dec(x_23);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
}
}
block_35:
{
lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_add(x_3, x_31);
x_33 = lean_array_uset(x_26, x_3, x_27);
x_3 = x_32;
x_4 = x_33;
x_9 = x_28;
x_10 = x_29;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_recBuildDefaultFacets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 7);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
x_13 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0(x_1, x_10, x_12, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_mk_string_unchecked("<collection>", 12, 12);
x_20 = l_Lake_Job_mixArray(lean_box(0), x_18, x_19);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_mk_string_unchecked("<collection>", 12, 12);
x_24 = l_Lake_Job_mixArray(lean_box(0), x_21, x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_13, 0, x_25);
return x_13;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_29 = x_14;
} else {
 lean_dec_ref(x_14);
 x_29 = lean_box(0);
}
x_30 = lean_mk_string_unchecked("<collection>", 12, 12);
x_31 = l_Lake_Job_mixArray(lean_box(0), x_27, x_30);
lean_dec(x_27);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_13, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_13, 0, x_39);
return x_13;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_dec(x_13);
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_43 = x_14;
} else {
 lean_dec_ref(x_14);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lake_LeanLib_recBuildDefaultFacets_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_1 = l_Lake_instDataKindUnit;
x_2 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_LeanLib_recBuildDefaultFacets), 7, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_6, 0, lean_box(0));
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
return x_7;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLib_defaultFacet;
x_3 = l_Lake_LeanLib_defaultFacetConfig;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_2, x_3);
x_5 = l_Lake_LeanLib_modulesFacet;
x_6 = l_Lake_LeanLib_modulesFacetConfig;
x_7 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_5, x_6);
x_8 = l_Lake_LeanLib_leanArtsFacet;
x_9 = l_Lake_LeanLib_leanArtsFacetConfig;
x_10 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_7, x_8, x_9);
x_11 = l_Lake_LeanLib_staticFacet;
x_12 = l_Lake_LeanLib_staticFacetConfig;
x_13 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_10, x_11, x_12);
x_14 = l_Lake_LeanLib_staticExportFacet;
x_15 = l_Lake_LeanLib_staticExportFacetConfig;
x_16 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_13, x_14, x_15);
x_17 = l_Lake_LeanLib_sharedFacet;
x_18 = l_Lake_LeanLib_sharedFacetConfig;
x_19 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_16, x_17, x_18);
x_20 = l_Lake_LeanLib_extraDepFacet;
x_21 = l_Lake_LeanLib_extraDepFacetConfig;
x_22 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_19, x_20, x_21);
return x_22;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanLib_initFacetConfigs;
return x_1;
}
}
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Library(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_LeanLib_modulesFacetConfig = _init_l_Lake_LeanLib_modulesFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_modulesFacetConfig);
l_Lake_LeanLib_leanArtsFacetConfig = _init_l_Lake_LeanLib_leanArtsFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacetConfig);
l_Lake_LeanLib_staticFacetConfig = _init_l_Lake_LeanLib_staticFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticFacetConfig);
l_Lake_LeanLib_staticExportFacetConfig = _init_l_Lake_LeanLib_staticExportFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacetConfig);
l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__7 = _init_l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__7();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_LeanLib_recBuildShared_spec__7);
l_Lake_LeanLib_sharedFacetConfig = _init_l_Lake_LeanLib_sharedFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_sharedFacetConfig);
l_Lake_LeanLib_extraDepFacetConfig = _init_l_Lake_LeanLib_extraDepFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacetConfig);
l_Lake_LeanLib_defaultFacetConfig = _init_l_Lake_LeanLib_defaultFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_defaultFacetConfig);
l_Lake_LeanLib_initFacetConfigs = _init_l_Lake_LeanLib_initFacetConfigs();
lean_mark_persistent(l_Lake_LeanLib_initFacetConfigs);
l_Lake_initLibraryFacetConfigs = _init_l_Lake_initLibraryFacetConfigs();
lean_mark_persistent(l_Lake_initLibraryFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
