// Lean compiler output
// Module: Lake.Build.Package
// Imports: Lake.Util.Git Lake.Util.Sugar Lake.Build.Common Lake.Build.Targets Lake.Build.Topological Lake.Reservoir
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
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPackageFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig;
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
extern lean_object* l_Lake_Package_depsFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lake_buildUnlessUpToDate_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ensureJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig;
lean_object* l_Lake_readTraceFile_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
extern lean_object* l_Lake_Package_gitHubReleaseFacet;
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fetchBuildArchive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindBool;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1(size_t, size_t, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lake_nullFormat___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_transDepsFacet;
lean_object* l_Array_extract(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___lam__0___boxed(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lake_instDecidableRelPosLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* l_Lake_Name_eraseHead(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_initFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_buildCacheFacet;
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instToStringBool;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
lean_object* l_Lake_Job_add(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runSpawnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OptDataKind_anonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_extraDepFacet;
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_MTime_checkUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lake_stdFormat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lake_uriEncode(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lake_FetchM_runJobM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_toolchain(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lake_EStateT_instMonadExceptOfOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_reservoirBarrelFacet;
extern lean_object* l_Lake_Package_optBuildCacheFacet;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_checkHashUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lake_EquipT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0(uint8_t, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_BuildInfo_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_4, x_3);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_12, 4);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___lam__0___boxed), 1, 0);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_16);
x_18 = l_Lean_Name_toString(x_17, x_8, x_16);
x_19 = lean_mk_string_unchecked(": package not found for dependency '", 36, 36);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = l_Lean_Name_toString(x_14, x_8, x_16);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("' (this is likely a bug in Lake)", 32, 32);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_box(3);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_array_get_size(x_6);
x_29 = lean_array_push(x_6, x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
lean_dec(x_14);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_box(0);
x_34 = lean_array_uset(x_4, x_3, x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_usize_of_nat(x_35);
x_37 = lean_usize_add(x_3, x_36);
x_38 = lean_array_uset(x_34, x_3, x_32);
x_3 = x_37;
x_4 = x_38;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_ctor_get(x_15, 4);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_19 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___lam__0___boxed), 1, 0);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
lean_inc(x_19);
x_21 = l_Lean_Name_toString(x_20, x_11, x_19);
x_22 = lean_mk_string_unchecked(": package not found for dependency '", 36, 36);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = l_Lean_Name_toString(x_17, x_11, x_19);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("' (this is likely a bug in Lake)", 32, 32);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = lean_box(3);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = lean_array_get_size(x_9);
x_32 = lean_array_push(x_9, x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_17);
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_box(0);
x_37 = lean_array_uset(x_4, x_3, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_usize_of_nat(x_38);
x_40 = lean_usize_add(x_3, x_39);
x_41 = lean_array_uset(x_37, x_3, x_35);
x_42 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(x_1, x_2, x_40, x_41, x_8, x_9, x_10);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_25 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
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
x_41 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_25 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
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
x_41 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_25 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
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
x_41 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg(x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_29 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_27);
x_30 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3), 9, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_27);
lean_closure_set(x_30, 2, x_29);
x_31 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg(x_26, x_30, x_3, x_4, x_5, x_6, x_7, x_25);
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
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_103 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(x_39, x_101, x_2, x_3, x_4, x_5, x_102, x_12);
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
x_105 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(x_39, x_104, x_2, x_3, x_4, x_5, x_37, x_12);
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
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0), 2, 1);
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
x_63 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0), 2, 1);
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
x_79 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__0), 2, 1);
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
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_19 = lean_mk_empty_array_with_capacity(x_5);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = lean_box(0);
x_22 = lean_mk_string_unchecked("<nil>", 5, 5);
x_23 = l_Lake_BuildTrace_nil(x_22);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_unbox(x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_25);
lean_ctor_set(x_13, 1, x_24);
x_26 = lean_task_pure(x_13);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_20);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_34 = lean_mk_empty_array_with_capacity(x_5);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = lean_box(0);
x_37 = lean_mk_string_unchecked("<nil>", 5, 5);
x_38 = l_Lake_BuildTrace_nil(x_37);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_unbox(x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_task_pure(x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_35);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_32);
lean_ctor_set(x_12, 0, x_46);
return x_12;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_ctor_get(x_13, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_50 = x_13;
} else {
 lean_dec_ref(x_13);
 x_50 = lean_box(0);
}
x_51 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_52 = lean_mk_empty_array_with_capacity(x_5);
x_53 = lean_mk_string_unchecked("", 0, 0);
x_54 = lean_box(0);
x_55 = lean_mk_string_unchecked("<nil>", 5, 5);
x_56 = l_Lake_BuildTrace_nil(x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_unbox(x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_58);
if (lean_is_scalar(x_50)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_50;
}
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_task_pure(x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_53);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_49);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_47);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_12);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_12, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_13);
if (x_68 == 0)
{
return x_12;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_13, 0);
x_70 = lean_ctor_get(x_13, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_13);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_12, 0, x_71);
return x_12;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_12, 1);
lean_inc(x_72);
lean_dec(x_12);
x_73 = lean_ctor_get(x_13, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_75 = x_13;
} else {
 lean_dec_ref(x_13);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 9);
lean_inc(x_8);
x_9 = lean_array_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_box_usize(x_9);
x_13 = lean_box_usize(x_11);
x_14 = lean_alloc_closure((void*)(l_Lake_Package_recFetchDeps___lam__0___boxed), 11, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_10);
x_15 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recFetchDeps___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Lake_Package_recFetchDeps___lam__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lake_Package_recFetchDeps_spec__0_spec__0___redArg___lam__0___boxed), 1, 0);
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
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
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
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
x_17 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0(x_2, x_15, x_16, x_3);
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
x_21 = l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1(x_18, x_20, x_2);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Json_compress(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_depsFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_3 = l_Lake_Package_keyword;
x_4 = lean_alloc_closure((void*)(l_Lake_Package_recFetchDeps), 7, 0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_depsFacetConfig___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_4, 0);
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
x_30 = lean_ctor_get(x_26, 0);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_ctor_get(x_2, 0);
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
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_2, x_27);
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
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_2, x_35);
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
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(x_43);
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
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(x_54);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7() {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_3, x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_uget(x_2, x_3);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_21, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_box(x_18);
x_25 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
lean_inc(x_25);
x_29 = l_Lean_Name_toString(x_26, x_28, x_25);
x_30 = lean_mk_string_unchecked(": package not found for dependency '", 36, 36);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_unbox(x_27);
x_33 = l_Lean_Name_toString(x_22, x_32, x_25);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = lean_mk_string_unchecked("' (this is likely a bug in Lake)", 32, 32);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_box(3);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_array_get_size(x_10);
x_41 = lean_array_push(x_10, x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_22);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_45 = lean_ctor_get(x_23, 0);
x_66 = l_Lake_Package_transDepsFacet;
x_67 = lean_ctor_get(x_45, 0);
lean_inc(x_67);
lean_ctor_set(x_23, 0, x_67);
x_68 = l_Lake_Package_keyword;
lean_inc(x_45);
x_69 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_69, 0, x_23);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_45);
lean_ctor_set(x_69, 3, x_66);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_70 = lean_apply_6(x_6, x_69, x_7, x_8, x_9, x_10, x_11);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_io_wait(x_75, x_72);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get_size(x_81);
x_84 = lean_nat_dec_lt(x_82, x_83);
if (x_84 == 0)
{
lean_dec(x_83);
lean_dec(x_81);
x_55 = x_80;
x_56 = x_74;
x_57 = x_79;
goto block_65;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_83, x_83);
if (x_85 == 0)
{
lean_dec(x_83);
lean_dec(x_81);
x_55 = x_80;
x_56 = x_74;
x_57 = x_79;
goto block_65;
}
else
{
lean_object* x_86; size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_box(0);
x_87 = lean_usize_of_nat(x_82);
x_88 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_89 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_81, x_87, x_88, x_86, x_74, x_79);
lean_dec(x_81);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_55 = x_80;
x_56 = x_92;
x_57 = x_91;
goto block_65;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_93 = lean_ctor_get(x_77, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_76, 1);
lean_inc(x_94);
lean_dec(x_76);
x_95 = lean_ctor_get(x_77, 0);
lean_inc(x_95);
lean_dec(x_77);
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_array_get_size(x_96);
x_99 = lean_nat_dec_lt(x_97, x_98);
if (x_99 == 0)
{
lean_dec(x_98);
lean_dec(x_96);
x_12 = x_95;
x_13 = x_74;
x_14 = x_94;
goto block_17;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_98, x_98);
if (x_100 == 0)
{
lean_dec(x_98);
lean_dec(x_96);
x_12 = x_95;
x_13 = x_74;
x_14 = x_94;
goto block_17;
}
else
{
lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_box(0);
x_102 = lean_usize_of_nat(x_97);
x_103 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_104 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_96, x_102, x_103, x_101, x_74, x_94);
lean_dec(x_96);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_12 = x_95;
x_13 = x_107;
x_14 = x_106;
goto block_17;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_70);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_70, 0);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_71);
if (x_110 == 0)
{
return x_70;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_71, 0);
x_112 = lean_ctor_get(x_71, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_71);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_70, 0, x_113);
return x_70;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_70, 1);
lean_inc(x_114);
lean_dec(x_70);
x_115 = lean_ctor_get(x_71, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_71, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_117 = x_71;
} else {
 lean_dec_ref(x_71);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_114);
return x_119;
}
}
block_54:
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_49 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_48, x_45);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_usize_of_nat(x_50);
x_52 = lean_usize_add(x_3, x_51);
x_3 = x_52;
x_5 = x_49;
x_10 = x_46;
x_11 = x_47;
goto _start;
}
block_65:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_55);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec(x_55);
x_46 = x_56;
x_47 = x_57;
x_48 = x_5;
goto block_54;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec(x_55);
x_46 = x_56;
x_47 = x_57;
x_48 = x_5;
goto block_54;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = lean_usize_of_nat(x_58);
x_63 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_64 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_55, x_62, x_63, x_5);
lean_dec(x_55);
x_46 = x_56;
x_47 = x_57;
x_48 = x_64;
goto block_54;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_120 = lean_ctor_get(x_23, 0);
lean_inc(x_120);
lean_dec(x_23);
x_141 = l_Lake_Package_transDepsFacet;
x_142 = lean_ctor_get(x_120, 0);
lean_inc(x_142);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l_Lake_Package_keyword;
lean_inc(x_120);
x_145 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_120);
lean_ctor_set(x_145, 3, x_141);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_146 = lean_apply_6(x_6, x_145, x_7, x_8, x_9, x_10, x_11);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_io_wait(x_151, x_148);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_unsigned_to_nat(0u);
x_159 = lean_array_get_size(x_157);
x_160 = lean_nat_dec_lt(x_158, x_159);
if (x_160 == 0)
{
lean_dec(x_159);
lean_dec(x_157);
x_130 = x_156;
x_131 = x_150;
x_132 = x_155;
goto block_140;
}
else
{
uint8_t x_161; 
x_161 = lean_nat_dec_le(x_159, x_159);
if (x_161 == 0)
{
lean_dec(x_159);
lean_dec(x_157);
x_130 = x_156;
x_131 = x_150;
x_132 = x_155;
goto block_140;
}
else
{
lean_object* x_162; size_t x_163; size_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_box(0);
x_163 = lean_usize_of_nat(x_158);
x_164 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_165 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_157, x_163, x_164, x_162, x_150, x_155);
lean_dec(x_157);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_130 = x_156;
x_131 = x_168;
x_132 = x_167;
goto block_140;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_120);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_169 = lean_ctor_get(x_153, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_152, 1);
lean_inc(x_170);
lean_dec(x_152);
x_171 = lean_ctor_get(x_153, 0);
lean_inc(x_171);
lean_dec(x_153);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_array_get_size(x_172);
x_175 = lean_nat_dec_lt(x_173, x_174);
if (x_175 == 0)
{
lean_dec(x_174);
lean_dec(x_172);
x_12 = x_171;
x_13 = x_150;
x_14 = x_170;
goto block_17;
}
else
{
uint8_t x_176; 
x_176 = lean_nat_dec_le(x_174, x_174);
if (x_176 == 0)
{
lean_dec(x_174);
lean_dec(x_172);
x_12 = x_171;
x_13 = x_150;
x_14 = x_170;
goto block_17;
}
else
{
lean_object* x_177; size_t x_178; size_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_177 = lean_box(0);
x_178 = lean_usize_of_nat(x_173);
x_179 = lean_usize_of_nat(x_174);
lean_dec(x_174);
x_180 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_172, x_178, x_179, x_177, x_150, x_170);
lean_dec(x_172);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_12 = x_171;
x_13 = x_183;
x_14 = x_182;
goto block_17;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_120);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_184 = lean_ctor_get(x_146, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_185 = x_146;
} else {
 lean_dec_ref(x_146);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_147, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_147, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_188 = x_147;
} else {
 lean_dec_ref(x_147);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
if (lean_is_scalar(x_185)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_185;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_184);
return x_190;
}
block_129:
{
lean_object* x_124; lean_object* x_125; size_t x_126; size_t x_127; 
x_124 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_123, x_120);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_usize_of_nat(x_125);
x_127 = lean_usize_add(x_3, x_126);
x_3 = x_127;
x_5 = x_124;
x_10 = x_121;
x_11 = x_122;
goto _start;
}
block_140:
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_array_get_size(x_130);
x_135 = lean_nat_dec_lt(x_133, x_134);
if (x_135 == 0)
{
lean_dec(x_134);
lean_dec(x_130);
x_121 = x_131;
x_122 = x_132;
x_123 = x_5;
goto block_129;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_134, x_134);
if (x_136 == 0)
{
lean_dec(x_134);
lean_dec(x_130);
x_121 = x_131;
x_122 = x_132;
x_123 = x_5;
goto block_129;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; 
x_137 = lean_usize_of_nat(x_133);
x_138 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_139 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_130, x_137, x_138, x_5);
lean_dec(x_130);
x_121 = x_131;
x_122 = x_132;
x_123 = x_139;
goto block_129;
}
}
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_5);
lean_ctor_set(x_191, 1, x_10);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_11);
return x_192;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_3, x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_uget(x_2, x_3);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 4);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_21, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_box(x_18);
x_25 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_stdFormat___at___Lake_Package_depsFacetConfig_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
lean_inc(x_25);
x_29 = l_Lean_Name_toString(x_26, x_28, x_25);
x_30 = lean_mk_string_unchecked(": package not found for dependency '", 36, 36);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_unbox(x_27);
x_33 = l_Lean_Name_toString(x_22, x_32, x_25);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = lean_mk_string_unchecked("' (this is likely a bug in Lake)", 32, 32);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_box(3);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_array_get_size(x_10);
x_41 = lean_array_push(x_10, x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_22);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_45 = lean_ctor_get(x_23, 0);
x_66 = l_Lake_Package_transDepsFacet;
x_67 = lean_ctor_get(x_45, 0);
lean_inc(x_67);
lean_ctor_set(x_23, 0, x_67);
x_68 = l_Lake_Package_keyword;
lean_inc(x_45);
x_69 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_69, 0, x_23);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_45);
lean_ctor_set(x_69, 3, x_66);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_70 = lean_apply_6(x_6, x_69, x_7, x_8, x_9, x_10, x_11);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_io_wait(x_75, x_72);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get_size(x_81);
x_84 = lean_nat_dec_lt(x_82, x_83);
if (x_84 == 0)
{
lean_dec(x_83);
lean_dec(x_81);
x_55 = x_80;
x_56 = x_74;
x_57 = x_79;
goto block_65;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_83, x_83);
if (x_85 == 0)
{
lean_dec(x_83);
lean_dec(x_81);
x_55 = x_80;
x_56 = x_74;
x_57 = x_79;
goto block_65;
}
else
{
lean_object* x_86; size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_box(0);
x_87 = lean_usize_of_nat(x_82);
x_88 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_89 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_81, x_87, x_88, x_86, x_74, x_79);
lean_dec(x_81);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_55 = x_80;
x_56 = x_92;
x_57 = x_91;
goto block_65;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_93 = lean_ctor_get(x_77, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_76, 1);
lean_inc(x_94);
lean_dec(x_76);
x_95 = lean_ctor_get(x_77, 0);
lean_inc(x_95);
lean_dec(x_77);
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_array_get_size(x_96);
x_99 = lean_nat_dec_lt(x_97, x_98);
if (x_99 == 0)
{
lean_dec(x_98);
lean_dec(x_96);
x_12 = x_95;
x_13 = x_74;
x_14 = x_94;
goto block_17;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_98, x_98);
if (x_100 == 0)
{
lean_dec(x_98);
lean_dec(x_96);
x_12 = x_95;
x_13 = x_74;
x_14 = x_94;
goto block_17;
}
else
{
lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_box(0);
x_102 = lean_usize_of_nat(x_97);
x_103 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_104 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_96, x_102, x_103, x_101, x_74, x_94);
lean_dec(x_96);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_12 = x_95;
x_13 = x_107;
x_14 = x_106;
goto block_17;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_45);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_70);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_70, 0);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_71);
if (x_110 == 0)
{
return x_70;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_71, 0);
x_112 = lean_ctor_get(x_71, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_71);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_70, 0, x_113);
return x_70;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_70, 1);
lean_inc(x_114);
lean_dec(x_70);
x_115 = lean_ctor_get(x_71, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_71, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_117 = x_71;
} else {
 lean_dec_ref(x_71);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_114);
return x_119;
}
}
block_54:
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_49 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_48, x_45);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_usize_of_nat(x_50);
x_52 = lean_usize_add(x_3, x_51);
x_53 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(x_1, x_2, x_52, x_4, x_49, x_6, x_7, x_8, x_9, x_46, x_47);
return x_53;
}
block_65:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_55);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec(x_55);
x_46 = x_56;
x_47 = x_57;
x_48 = x_5;
goto block_54;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec(x_55);
x_46 = x_56;
x_47 = x_57;
x_48 = x_5;
goto block_54;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = lean_usize_of_nat(x_58);
x_63 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_64 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_55, x_62, x_63, x_5);
lean_dec(x_55);
x_46 = x_56;
x_47 = x_57;
x_48 = x_64;
goto block_54;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_120 = lean_ctor_get(x_23, 0);
lean_inc(x_120);
lean_dec(x_23);
x_141 = l_Lake_Package_transDepsFacet;
x_142 = lean_ctor_get(x_120, 0);
lean_inc(x_142);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l_Lake_Package_keyword;
lean_inc(x_120);
x_145 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_120);
lean_ctor_set(x_145, 3, x_141);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_146 = lean_apply_6(x_6, x_145, x_7, x_8, x_9, x_10, x_11);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_io_wait(x_151, x_148);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_unsigned_to_nat(0u);
x_159 = lean_array_get_size(x_157);
x_160 = lean_nat_dec_lt(x_158, x_159);
if (x_160 == 0)
{
lean_dec(x_159);
lean_dec(x_157);
x_130 = x_156;
x_131 = x_150;
x_132 = x_155;
goto block_140;
}
else
{
uint8_t x_161; 
x_161 = lean_nat_dec_le(x_159, x_159);
if (x_161 == 0)
{
lean_dec(x_159);
lean_dec(x_157);
x_130 = x_156;
x_131 = x_150;
x_132 = x_155;
goto block_140;
}
else
{
lean_object* x_162; size_t x_163; size_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_box(0);
x_163 = lean_usize_of_nat(x_158);
x_164 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_165 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_157, x_163, x_164, x_162, x_150, x_155);
lean_dec(x_157);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_130 = x_156;
x_131 = x_168;
x_132 = x_167;
goto block_140;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_120);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_169 = lean_ctor_get(x_153, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_152, 1);
lean_inc(x_170);
lean_dec(x_152);
x_171 = lean_ctor_get(x_153, 0);
lean_inc(x_171);
lean_dec(x_153);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_array_get_size(x_172);
x_175 = lean_nat_dec_lt(x_173, x_174);
if (x_175 == 0)
{
lean_dec(x_174);
lean_dec(x_172);
x_12 = x_171;
x_13 = x_150;
x_14 = x_170;
goto block_17;
}
else
{
uint8_t x_176; 
x_176 = lean_nat_dec_le(x_174, x_174);
if (x_176 == 0)
{
lean_dec(x_174);
lean_dec(x_172);
x_12 = x_171;
x_13 = x_150;
x_14 = x_170;
goto block_17;
}
else
{
lean_object* x_177; size_t x_178; size_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_177 = lean_box(0);
x_178 = lean_usize_of_nat(x_173);
x_179 = lean_usize_of_nat(x_174);
lean_dec(x_174);
x_180 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_172, x_178, x_179, x_177, x_150, x_170);
lean_dec(x_172);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_12 = x_171;
x_13 = x_183;
x_14 = x_182;
goto block_17;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_120);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_184 = lean_ctor_get(x_146, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_185 = x_146;
} else {
 lean_dec_ref(x_146);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_147, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_147, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_188 = x_147;
} else {
 lean_dec_ref(x_147);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
if (lean_is_scalar(x_185)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_185;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_184);
return x_190;
}
block_129:
{
lean_object* x_124; lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; 
x_124 = l_Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0(x_123, x_120);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_usize_of_nat(x_125);
x_127 = lean_usize_add(x_3, x_126);
x_128 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(x_1, x_2, x_127, x_4, x_124, x_6, x_7, x_8, x_9, x_121, x_122);
return x_128;
}
block_140:
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_array_get_size(x_130);
x_135 = lean_nat_dec_lt(x_133, x_134);
if (x_135 == 0)
{
lean_dec(x_134);
lean_dec(x_130);
x_121 = x_131;
x_122 = x_132;
x_123 = x_5;
goto block_129;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_134, x_134);
if (x_136 == 0)
{
lean_dec(x_134);
lean_dec(x_130);
x_121 = x_131;
x_122 = x_132;
x_123 = x_5;
goto block_129;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; 
x_137 = lean_usize_of_nat(x_133);
x_138 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_139 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_130, x_137, x_138, x_5);
lean_dec(x_130);
x_121 = x_131;
x_122 = x_132;
x_123 = x_139;
goto block_129;
}
}
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_5);
lean_ctor_set(x_191, 1, x_10);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_11);
return x_192;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_32; 
x_32 = lean_nat_dec_lt(x_1, x_2);
if (x_32 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_12 = x_3;
x_13 = x_10;
x_14 = x_11;
goto block_31;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_2, x_2);
if (x_33 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_12 = x_3;
x_13 = x_10;
x_14 = x_11;
goto block_31;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_usize_of_nat(x_1);
x_35 = lean_usize_of_nat(x_2);
x_36 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8(x_4, x_5, x_34, x_35, x_3, x_6, x_7, x_8, x_9, x_10, x_11);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_12 = x_39;
x_13 = x_40;
x_14 = x_38;
goto block_31;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_36, 0, x_46);
return x_36;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_dec(x_36);
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
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
}
block_31:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_17 = lean_mk_empty_array_with_capacity(x_1);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = lean_box(0);
x_20 = lean_mk_string_unchecked("<nil>", 5, 5);
x_21 = l_Lake_BuildTrace_nil(x_20);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unbox(x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_task_pure(x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_18);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_13);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7;
x_9 = lean_ctor_get(x_1, 9);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_recComputeTransDeps___lam__0___boxed), 11, 5);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_1);
lean_closure_set(x_12, 4, x_9);
x_13 = l_Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2(x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lake_OrdHashSet_insert___at___Lake_Package_recComputeTransDeps_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__6(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8_spec__8(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_Package_recComputeTransDeps_spec__8(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_Package_recComputeTransDeps___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_depsFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_3 = l_Lake_Package_keyword;
x_4 = lean_alloc_closure((void*)(l_Lake_Package_recComputeTransDeps), 7, 0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*25 + 2);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lake_Package_optReservoirBarrelFacet;
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lake_Package_keyword;
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_10);
x_15 = lean_apply_6(x_2, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = l_Lake_Package_optGitHubReleaseFacet;
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lake_Package_keyword;
x_20 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_16);
x_21 = lean_apply_6(x_2, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("false", 5, 5);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_mk_string_unchecked("true", 4, 4);
return x_4;
}
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_5, 0, x_2);
x_6 = l_Lean_Json_compress(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__0), 7, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed), 2, 0);
x_3 = l_Lake_instDataKindBool;
x_4 = l_Lake_Package_keyword;
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_stdFormat___at___Lake_Package_optBuildCacheFacetConfig_spec__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_Package_optBuildCacheFacetConfig___lam__1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_5, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get_uint8(x_77, sizeof(void*)*11);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_box(1);
x_80 = lean_unbox(x_79);
x_49 = x_80;
x_50 = x_6;
x_51 = x_7;
goto block_75;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_box(0);
x_82 = lean_unbox(x_81);
x_49 = x_82;
x_50 = x_6;
x_51 = x_7;
goto block_75;
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lake_Package_optBuildCacheFacet;
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lake_Package_keyword;
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_10);
x_15 = lean_apply_6(x_2, x_14, x_3, x_4, x_5, x_8, x_9);
return x_15;
}
block_35:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_box(1);
x_21 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_mk_string_unchecked("", 0, 0);
x_25 = lean_box(0);
x_26 = lean_mk_string_unchecked("<nil>", 5, 5);
x_27 = l_Lake_BuildTrace_nil(x_26);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unbox(x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_task_pure(x_30);
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_19);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_18);
return x_34;
}
block_39:
{
if (x_38 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = x_36;
x_18 = x_37;
x_19 = x_38;
goto block_35;
}
else
{
x_8 = x_36;
x_9 = x_37;
goto block_16;
}
}
block_48:
{
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = x_40;
x_18 = x_42;
x_19 = x_44;
goto block_35;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_string_utf8_byte_size(x_43);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_instDecidableEqPos(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
x_8 = x_40;
x_9 = x_42;
goto block_16;
}
else
{
x_36 = x_40;
x_37 = x_42;
x_38 = x_41;
goto block_39;
}
}
}
block_75:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 6);
lean_inc(x_54);
x_55 = l_System_FilePath_normalize(x_54);
x_56 = l_Lake_joinRelative(x_52, x_55);
lean_dec(x_55);
x_57 = l_System_FilePath_pathExists(x_56, x_51);
lean_dec(x_56);
if (x_49 == 0)
{
lean_object* x_58; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_17 = x_50;
x_18 = x_58;
x_19 = x_49;
goto block_35;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = lean_ctor_get_uint8(x_53, sizeof(void*)*25 + 2);
lean_dec(x_53);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_5, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lake_Env_toolchain(x_64);
lean_dec(x_64);
x_66 = lean_ctor_get(x_1, 7);
lean_inc(x_66);
x_67 = lean_mk_string_unchecked("leanprover", 10, 10);
x_68 = lean_string_dec_eq(x_66, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_mk_string_unchecked("leanprover-community", 20, 20);
x_70 = lean_string_dec_eq(x_66, x_69);
lean_dec(x_69);
lean_dec(x_66);
x_40 = x_50;
x_41 = x_61;
x_42 = x_62;
x_43 = x_65;
x_44 = x_70;
goto block_48;
}
else
{
lean_dec(x_66);
x_40 = x_50;
x_41 = x_61;
x_42 = x_62;
x_43 = x_65;
x_44 = x_68;
goto block_48;
}
}
else
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
lean_dec(x_57);
x_36 = x_50;
x_37 = x_71;
x_38 = x_61;
goto block_39;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_dec(x_57);
x_73 = lean_box(0);
x_74 = lean_unbox(x_73);
x_17 = x_50;
x_18 = x_72;
x_19 = x_74;
goto block_35;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1 + 3);
x_12 = lean_box(2);
x_13 = lean_unbox(x_12);
x_14 = l_Lake_instDecidableEqVerbosity(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_19 = lean_mk_string_unchecked(" (see '", 7, 7);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
lean_inc(x_18);
x_21 = l_Lean_Name_toString(x_20, x_14, x_18);
x_22 = lean_string_append(x_19, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked(":", 1, 1);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = l_Lake_Name_eraseHead(x_2);
x_26 = l_Lean_Name_toString(x_25, x_14, x_18);
x_27 = lean_string_append(x_24, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("' for details)", 14, 14);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
x_15 = lean_box(2);
x_16 = lean_unbox(x_15);
x_17 = l_Lake_instDecidableEqVerbosity(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_22 = lean_mk_string_unchecked(" (see '", 7, 7);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_21);
x_24 = l_Lean_Name_toString(x_23, x_17, x_21);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked(":", 1, 1);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l_Lake_Name_eraseHead(x_2);
x_29 = l_Lean_Name_toString(x_28, x_17, x_21);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("' for details)", 14, 14);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_12);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = l_Lake_BuildTrace_mix(x_1, x_11);
x_13 = lean_apply_1(x_2, x_9);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_13, x_18, x_3, x_4, x_5, x_6, x_16, x_8);
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_string_utf8_byte_size(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_instDecidableEqPos(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_30 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_24, x_26, x_27);
x_31 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_24, x_30, x_26);
x_32 = lean_string_utf8_extract(x_24, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_24);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
x_38 = lean_box(0);
x_39 = lean_array_push(x_37, x_35);
x_40 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_40);
x_43 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(x_25, x_38, x_3, x_4, x_5, x_6, x_42, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_26);
lean_dec(x_24);
x_44 = lean_box(0);
x_45 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(x_25, x_44, x_3, x_4, x_5, x_6, x_23, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_19, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_19, 0, x_51);
return x_19;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
lean_dec(x_19);
x_53 = lean_ctor_get(x_20, 0);
lean_inc(x_53);
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
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_7);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_7);
lean_ctor_set(x_59, 1, x_8);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_7, 0);
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_7);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_8);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__1), 8, 6);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_6);
lean_closure_set(x_11, 4, x_7);
lean_closure_set(x_11, 5, x_8);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_io_map_task(x_11, x_12, x_3, x_4, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_instDataKindUnit;
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lake_instDataKindUnit;
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
if (x_2 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_43, sizeof(void*)*25 + 2);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_dec(x_7);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_46);
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*1 + 3);
x_51 = lean_box(2);
x_52 = lean_unbox(x_51);
x_53 = l_Lake_instDecidableEqVerbosity(x_50, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_1);
x_54 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
x_9 = x_54;
x_10 = x_48;
x_11 = x_8;
goto block_25;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_box(x_44);
x_56 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 2, 1);
lean_closure_set(x_56, 0, x_55);
x_57 = l_Lake_Package_optReservoirBarrelFacet;
x_58 = lean_mk_string_unchecked(" (see '", 7, 7);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
lean_inc(x_56);
x_60 = l_Lean_Name_toString(x_59, x_53, x_56);
x_61 = lean_string_append(x_58, x_60);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked(":", 1, 1);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = l_Lake_Name_eraseHead(x_57);
x_65 = l_Lean_Name_toString(x_64, x_53, x_56);
x_66 = lean_string_append(x_63, x_65);
lean_dec(x_65);
x_67 = lean_mk_string_unchecked("' for details)", 14, 14);
x_68 = lean_string_append(x_66, x_67);
lean_dec(x_67);
x_9 = x_68;
x_10 = x_48;
x_11 = x_8;
goto block_25;
}
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; 
x_69 = lean_ctor_get(x_7, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_dec(x_7);
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_70);
x_73 = lean_ctor_get(x_6, 0);
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*1 + 3);
x_75 = lean_box(2);
x_76 = lean_unbox(x_75);
x_77 = l_Lake_instDecidableEqVerbosity(x_74, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_1);
x_78 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
x_26 = x_78;
x_27 = x_72;
x_28 = x_8;
goto block_42;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_box(x_2);
x_80 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed), 2, 1);
lean_closure_set(x_80, 0, x_79);
x_81 = l_Lake_Package_optGitHubReleaseFacet;
x_82 = lean_mk_string_unchecked(" (see '", 7, 7);
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
lean_dec(x_1);
lean_inc(x_80);
x_84 = l_Lean_Name_toString(x_83, x_77, x_80);
x_85 = lean_string_append(x_82, x_84);
lean_dec(x_84);
x_86 = lean_mk_string_unchecked(":", 1, 1);
x_87 = lean_string_append(x_85, x_86);
lean_dec(x_86);
x_88 = l_Lake_Name_eraseHead(x_81);
x_89 = l_Lean_Name_toString(x_88, x_77, x_80);
x_90 = lean_string_append(x_87, x_89);
lean_dec(x_89);
x_91 = lean_mk_string_unchecked("' for details)", 14, 14);
x_92 = lean_string_append(x_90, x_91);
lean_dec(x_91);
x_26 = x_92;
x_27 = x_72;
x_28 = x_8;
goto block_42;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_7);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_8);
return x_95;
}
block_25:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_mk_string_unchecked("building from source; failed to fetch Reservoir build", 53, 53);
x_13 = lean_string_append(x_12, x_9);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = lean_box(0);
x_19 = lean_array_push(x_17, x_15);
x_20 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
block_42:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_mk_string_unchecked("building from source; failed to fetch GitHub release", 52, 52);
x_30 = lean_string_append(x_29, x_26);
lean_dec(x_26);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
x_35 = lean_box(0);
x_36 = lean_array_push(x_34, x_32);
x_37 = lean_ctor_get_uint8(x_27, sizeof(void*)*2);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_28);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lake_Package_maybeFetchBuildCache(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__3___boxed), 8, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(0);
x_16 = lean_mk_string_unchecked("<nil>", 5, 5);
x_17 = l_Lake_BuildTrace_nil(x_16);
x_18 = lean_unbox(x_15);
x_19 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_12, x_13, x_14, x_18, x_2, x_3, x_4, x_5, x_17, x_10);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_9, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__3___boxed), 8, 1);
lean_closure_set(x_27, 0, x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_box(0);
x_30 = lean_mk_string_unchecked("<nil>", 5, 5);
x_31 = l_Lake_BuildTrace_nil(x_30);
x_32 = lean_unbox(x_29);
x_33 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_25, x_27, x_28, x_32, x_2, x_3, x_4, x_5, x_31, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_26);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_9);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_8, 0, x_44);
return x_8;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_dec(x_8);
x_46 = lean_ctor_get(x_9, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_48 = x_9;
} else {
 lean_dec_ref(x_9);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__3(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchOptRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_maybeFetchBuildCacheWithWarning(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lake_Package_fetchTargetJob(x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lake_Job_mix___redArg(x_5, x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_21;
x_10 = x_20;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_16, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_16, 0, x_31);
return x_16;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_35 = x_17;
} else {
 lean_dec_ref(x_17);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l_Lake_instDataKindUnit;
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
x_103 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_39, x_101, x_2, x_3, x_4, x_5, x_102, x_12);
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
x_105 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_39, x_104, x_2, x_3, x_4, x_5, x_37, x_12);
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
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
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
x_63 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
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
x_79 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__0), 2, 1);
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
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_name_eq(x_3, x_22);
lean_dec(x_22);
x_24 = l_instDecidableNot___redArg(x_23);
if (x_24 == 0)
{
x_11 = x_4;
x_12 = x_9;
x_13 = x_10;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_25 = l_Lake_Package_maybeFetchBuildCacheWithWarning(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lake_Job_add(lean_box(0), lean_box(0), x_4, x_28);
x_11 = x_30;
x_12 = x_29;
x_13 = x_27;
goto block_19;
}
else
{
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_25;
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_array_size(x_15);
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0(x_1, x_15, x_16, x_17, x_11, x_5, x_6, x_7, x_8, x_12, x_13);
lean_dec(x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_8 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_9);
x_12 = l_Lean_Name_toString(x_9, x_11, x_8);
x_13 = lean_mk_string_unchecked(":extraDep", 9, 9);
x_14 = lean_mk_string_unchecked("@", 1, 1);
x_15 = lean_string_append(x_14, x_12);
x_16 = lean_string_append(x_15, x_13);
x_17 = lean_box(0);
x_18 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_21 = lean_box(0);
x_22 = l_Lake_BuildTrace_nil(x_16);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_task_pure(x_25);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_30);
x_31 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 10, 4);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_19);
lean_closure_set(x_31, 2, x_9);
lean_closure_set(x_31, 3, x_29);
lean_inc(x_5);
x_32 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(x_31, x_2, x_3, x_4, x_5, x_6, x_7);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_5, 3);
lean_inc(x_37);
lean_dec(x_5);
x_38 = lean_st_ref_take(x_37, x_34);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
x_45 = lean_unbox(x_28);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_45);
x_46 = l_Lake_Job_toOpaque___redArg(x_44);
x_47 = lean_array_push(x_39, x_46);
x_48 = lean_st_ref_set(x_37, x_47, x_40);
lean_dec(x_37);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = l_Lake_Job_renew___redArg(x_44);
lean_ctor_set(x_33, 0, x_51);
lean_ctor_set(x_48, 0, x_33);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = l_Lake_Job_renew___redArg(x_44);
lean_ctor_set(x_33, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_33);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_55 = lean_ctor_get(x_33, 0);
x_56 = lean_ctor_get(x_33, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_33);
x_57 = lean_ctor_get(x_5, 3);
lean_inc(x_57);
lean_dec(x_5);
x_58 = lean_st_ref_take(x_57, x_34);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_61);
x_65 = lean_unbox(x_28);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_65);
x_66 = l_Lake_Job_toOpaque___redArg(x_64);
x_67 = lean_array_push(x_59, x_66);
x_68 = lean_st_ref_set(x_57, x_67, x_60);
lean_dec(x_57);
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
lean_ctor_set(x_72, 1, x_56);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lake_Package_recBuildExtraDepTargets_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_recBuildExtraDepTargets___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = l_Lake_instDataKindUnit;
x_2 = l_Lake_Package_keyword;
x_3 = lean_alloc_closure((void*)(l_Lake_Package_recBuildExtraDepTargets), 7, 0);
x_4 = lean_box(1);
x_5 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_5, 0, lean_box(0));
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_5);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 7);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_instDecidableEqPos(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_mk_string_unchecked("HEAD", 4, 4);
x_11 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_12 = lean_mk_string_unchecked("--verify", 8, 8);
x_13 = lean_mk_string_unchecked("--end-of-options", 16, 16);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_10);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 0, 3);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, 0, x_22);
x_23 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, 1, x_23);
x_24 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, 2, x_24);
x_25 = lean_mk_string_unchecked("git", 3, 3);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_9);
x_27 = lean_mk_empty_array_with_capacity(x_7);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_30);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_8);
x_31 = l_Lake_captureProc_x3f(x_29, x_4);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec(x_3);
x_38 = lean_mk_string_unchecked("failed to resolve HEAD revision", 31, 31);
x_39 = lean_box(3);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_41);
x_42 = lean_array_get_size(x_35);
x_43 = lean_array_push(x_35, x_40);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_31, 0, x_45);
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
lean_dec(x_3);
x_50 = lean_mk_string_unchecked("failed to resolve HEAD revision", 31, 31);
x_51 = lean_box(3);
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
x_54 = lean_array_get_size(x_47);
x_55 = lean_array_push(x_47, x_52);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_46);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_31);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_60 = lean_ctor_get(x_31, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_3, 0);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_63 = lean_ctor_get(x_3, 1);
lean_inc(x_63);
lean_dec(x_3);
x_64 = lean_ctor_get(x_32, 0);
lean_inc(x_64);
lean_dec(x_32);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lake_Env_toolchain(x_66);
x_68 = lean_string_utf8_byte_size(x_67);
x_69 = l_instDecidableEqPos(x_68, x_7);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_box(x_8);
x_71 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 2, 1);
lean_closure_set(x_71, 0, x_70);
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
lean_dec(x_1);
x_73 = l_Lean_Name_toString(x_72, x_8, x_71);
x_74 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_63);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_62);
x_75 = l_Lake_Reservoir_pkgApiUrl(x_66, x_5, x_73);
lean_dec(x_73);
lean_dec(x_5);
x_76 = lean_mk_string_unchecked("/barrel\?rev=", 12, 12);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = lean_string_append(x_77, x_64);
lean_dec(x_64);
x_79 = lean_mk_string_unchecked("&toolchain=", 11, 11);
x_80 = lean_string_append(x_78, x_79);
lean_dec(x_79);
x_81 = l_Lake_uriEncode(x_67);
lean_dec(x_67);
x_82 = lean_string_append(x_80, x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_31, 0, x_83);
return x_31;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_5);
lean_dec(x_1);
x_84 = lean_mk_string_unchecked("Lean toolchain not known; Reservoir only hosts builds for known toolchains", 74, 74);
x_85 = lean_box(3);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
x_88 = lean_array_get_size(x_61);
x_89 = lean_array_push(x_61, x_86);
x_90 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_63);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_62);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_31, 0, x_91);
return x_31;
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_92 = lean_ctor_get(x_31, 1);
lean_inc(x_92);
lean_dec(x_31);
x_93 = lean_ctor_get(x_3, 0);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
lean_dec(x_3);
x_96 = lean_ctor_get(x_32, 0);
lean_inc(x_96);
lean_dec(x_32);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
lean_dec(x_2);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lake_Env_toolchain(x_98);
x_100 = lean_string_utf8_byte_size(x_99);
x_101 = l_instDecidableEqPos(x_100, x_7);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_102 = lean_box(x_8);
x_103 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 2, 1);
lean_closure_set(x_103, 0, x_102);
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
lean_dec(x_1);
x_105 = l_Lean_Name_toString(x_104, x_8, x_103);
x_106 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_106, 0, x_93);
lean_ctor_set(x_106, 1, x_95);
lean_ctor_set_uint8(x_106, sizeof(void*)*2, x_94);
x_107 = l_Lake_Reservoir_pkgApiUrl(x_98, x_5, x_105);
lean_dec(x_105);
lean_dec(x_5);
x_108 = lean_mk_string_unchecked("/barrel\?rev=", 12, 12);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = lean_string_append(x_109, x_96);
lean_dec(x_96);
x_111 = lean_mk_string_unchecked("&toolchain=", 11, 11);
x_112 = lean_string_append(x_110, x_111);
lean_dec(x_111);
x_113 = l_Lake_uriEncode(x_99);
lean_dec(x_99);
x_114 = lean_string_append(x_112, x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_106);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_92);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_5);
lean_dec(x_1);
x_117 = lean_mk_string_unchecked("Lean toolchain not known; Reservoir only hosts builds for known toolchains", 74, 74);
x_118 = lean_box(3);
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
x_120 = lean_unbox(x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_120);
x_121 = lean_array_get_size(x_93);
x_122 = lean_array_push(x_93, x_119);
x_123 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_95);
lean_ctor_set_uint8(x_123, sizeof(void*)*2, x_94);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_92);
return x_125;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_mk_string_unchecked("package has no Reservoir scope", 30, 30);
x_127 = lean_box(3);
x_128 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_128, 0, x_126);
x_129 = lean_unbox(x_127);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_129);
x_130 = lean_ctor_get(x_3, 0);
lean_inc(x_130);
x_131 = lean_array_get_size(x_130);
x_132 = lean_array_push(x_130, x_128);
x_133 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
lean_dec(x_3);
x_135 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_133);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_4);
return x_137;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getBarrelUrl___redArg(x_1, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getBarrelUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getBarrelUrl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_99; lean_object* x_140; lean_object* x_141; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_140 = lean_ctor_get(x_1, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 11);
lean_inc(x_141);
lean_dec(x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_1, 8);
lean_inc(x_142);
x_143 = lean_string_utf8_byte_size(x_142);
x_144 = lean_unsigned_to_nat(0u);
x_145 = l_instDecidableEqPos(x_143, x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_dec(x_142);
x_99 = x_141;
goto block_139;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_142);
x_99 = x_146;
goto block_139;
}
}
else
{
x_99 = x_141;
goto block_139;
}
block_20:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_mk_string_unchecked("no release tag found for revision", 33, 33);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = lean_box(3);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = lean_array_push(x_12, x_10);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
block_98:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_27 = lean_mk_string_unchecked("HEAD", 4, 4);
x_28 = lean_mk_string_unchecked("describe", 8, 8);
x_29 = lean_mk_string_unchecked("--tags", 6, 6);
x_30 = lean_mk_string_unchecked("--exact-match", 13, 13);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_mk_empty_array_with_capacity(x_31);
lean_inc(x_32);
x_33 = lean_array_push(x_32, x_28);
x_34 = lean_array_push(x_33, x_29);
x_35 = lean_array_push(x_34, x_30);
lean_inc(x_27);
x_36 = lean_array_push(x_35, x_27);
x_37 = lean_box(1);
x_38 = lean_alloc_ctor(0, 0, 3);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, 0, x_39);
x_40 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, 1, x_40);
x_41 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, 2, x_41);
x_42 = lean_mk_string_unchecked("git", 3, 3);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_21);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_mk_empty_array_with_capacity(x_44);
x_46 = lean_box(1);
x_47 = lean_box(0);
lean_inc(x_45);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_38);
x_48 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_36);
lean_ctor_set(x_48, 3, x_43);
lean_ctor_set(x_48, 4, x_45);
x_49 = lean_unbox(x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_49);
x_50 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 1, x_50);
x_51 = l_Lake_captureProc_x3f(x_48, x_25);
lean_dec(x_48);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_26);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_55 = lean_mk_string_unchecked("--verify", 8, 8);
x_56 = lean_mk_string_unchecked("--end-of-options", 16, 16);
x_57 = lean_array_push(x_32, x_54);
x_58 = lean_array_push(x_57, x_55);
x_59 = lean_array_push(x_58, x_56);
x_60 = lean_array_push(x_59, x_27);
x_61 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_61, 0, x_38);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_43);
lean_ctor_set(x_61, 4, x_45);
x_62 = lean_unbox(x_46);
lean_ctor_set_uint8(x_61, sizeof(void*)*5, x_62);
x_63 = lean_unbox(x_47);
lean_ctor_set_uint8(x_61, sizeof(void*)*5 + 1, x_63);
x_64 = l_Lake_captureProc_x3f(x_61, x_53);
lean_dec(x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_24);
lean_ctor_set(x_67, 1, x_23);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_22);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_68; 
x_68 = lean_mk_string_unchecked("", 0, 0);
x_4 = x_68;
x_5 = x_67;
x_6 = x_66;
goto block_20;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_mk_string_unchecked(" '", 2, 2);
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = lean_mk_string_unchecked("'", 1, 1);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_4 = x_73;
x_5 = x_67;
x_6 = x_66;
goto block_20;
}
}
else
{
uint8_t x_74; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_27);
x_74 = !lean_is_exclusive(x_51);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_51, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_52, 0);
lean_inc(x_76);
lean_dec(x_52);
x_77 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_77, 0, x_24);
lean_ctor_set(x_77, 1, x_23);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_22);
x_78 = lean_mk_string_unchecked("/releases/download/", 19, 19);
x_79 = lean_string_append(x_26, x_78);
lean_dec(x_78);
x_80 = lean_string_append(x_79, x_76);
lean_dec(x_76);
x_81 = lean_mk_string_unchecked("/", 1, 1);
x_82 = lean_string_append(x_80, x_81);
lean_dec(x_81);
x_83 = lean_ctor_get(x_1, 16);
lean_inc(x_83);
lean_dec(x_1);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_51, 0, x_85);
return x_51;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_86 = lean_ctor_get(x_51, 1);
lean_inc(x_86);
lean_dec(x_51);
x_87 = lean_ctor_get(x_52, 0);
lean_inc(x_87);
lean_dec(x_52);
x_88 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_88, 0, x_24);
lean_ctor_set(x_88, 1, x_23);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_22);
x_89 = lean_mk_string_unchecked("/releases/download/", 19, 19);
x_90 = lean_string_append(x_26, x_89);
lean_dec(x_89);
x_91 = lean_string_append(x_90, x_87);
lean_dec(x_87);
x_92 = lean_mk_string_unchecked("/", 1, 1);
x_93 = lean_string_append(x_91, x_92);
lean_dec(x_92);
x_94 = lean_ctor_get(x_1, 16);
lean_inc(x_94);
lean_dec(x_1);
x_95 = lean_string_append(x_93, x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_88);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_86);
return x_97;
}
}
}
block_139:
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_mk_string_unchecked("origin", 6, 6);
lean_inc(x_21);
x_101 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_100, x_21, x_3);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
lean_dec(x_21);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_104 = lean_ctor_get(x_101, 0);
lean_dec(x_104);
x_105 = lean_ctor_get(x_2, 0);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_107 = lean_ctor_get(x_2, 1);
lean_inc(x_107);
lean_dec(x_2);
x_108 = lean_mk_string_unchecked("release repository URL not known; the package may need to set 'releaseRepo'", 75, 75);
x_109 = lean_box(3);
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
x_111 = lean_unbox(x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_111);
x_112 = lean_array_get_size(x_105);
x_113 = lean_array_push(x_105, x_110);
x_114 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_106);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_101, 0, x_115);
return x_101;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_116 = lean_ctor_get(x_101, 1);
lean_inc(x_116);
lean_dec(x_101);
x_117 = lean_ctor_get(x_2, 0);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
lean_dec(x_2);
x_120 = lean_mk_string_unchecked("release repository URL not known; the package may need to set 'releaseRepo'", 75, 75);
x_121 = lean_box(3);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_120);
x_123 = lean_unbox(x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_123);
x_124 = lean_array_get_size(x_117);
x_125 = lean_array_push(x_117, x_122);
x_126 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_119);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_118);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_116);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_101, 1);
lean_inc(x_129);
lean_dec(x_101);
x_130 = lean_ctor_get(x_2, 0);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_132 = lean_ctor_get(x_2, 1);
lean_inc(x_132);
lean_dec(x_2);
x_133 = lean_ctor_get(x_102, 0);
lean_inc(x_133);
lean_dec(x_102);
x_22 = x_131;
x_23 = x_132;
x_24 = x_130;
x_25 = x_129;
x_26 = x_133;
goto block_98;
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_101, 1);
lean_inc(x_134);
lean_dec(x_101);
x_135 = lean_ctor_get(x_2, 0);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_137 = lean_ctor_get(x_2, 1);
lean_inc(x_137);
lean_dec(x_2);
x_138 = lean_ctor_get(x_99, 0);
lean_inc(x_138);
lean_dec(x_99);
x_22 = x_136;
x_23 = x_137;
x_24 = x_135;
x_25 = x_134;
x_26 = x_138;
goto block_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getReleaseUrl___redArg(x_1, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_getReleaseUrl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_Package_getReleaseUrl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = l_Lake_download(x_1, x_2, x_3, x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_15);
lean_ctor_set(x_12, 1, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_29 = x_12;
} else {
 lean_dec_ref(x_12);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_25);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_11, 0);
lean_dec(x_34);
x_35 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_12, 1);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_35);
lean_ctor_set(x_12, 1, x_39);
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_11, 0, x_43);
return x_11;
}
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_dec(x_11);
x_45 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_dec(x_8);
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_12, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_49 = x_12;
} else {
 lean_dec_ref(x_12);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_45);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_29; 
x_15 = l_System_FilePath_pathExists(x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_closure((void*)(l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0___boxed), 9, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(1);
x_29 = lean_unbox(x_16);
lean_dec(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_9);
x_30 = lean_ctor_get(x_6, 3);
lean_inc(x_30);
x_31 = l_Lake_MTime_checkUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_5, x_30, x_17);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_21);
x_36 = lean_unbox(x_33);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_free_object(x_31);
x_37 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_19, x_8, x_4, x_10, x_11, x_12, x_35, x_34);
lean_dec(x_7);
lean_dec(x_6);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_31, 0, x_38);
return x_31;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_20);
lean_ctor_set(x_41, 1, x_22);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_21);
x_42 = lean_unbox(x_39);
lean_dec(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_19, x_8, x_4, x_10, x_11, x_12, x_41, x_40);
lean_dec(x_7);
lean_dec(x_6);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_23);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_7);
x_46 = l_Lake_readTraceFile_x3f(x_7, x_20, x_17);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_22);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_21);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_62; uint8_t x_63; 
lean_dec(x_18);
x_53 = l_Lake_MTime_checkUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__0(x_5, x_9, x_48);
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
x_62 = lean_ctor_get(x_12, 0);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*1);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_54);
x_57 = x_63;
goto block_61;
}
else
{
uint8_t x_64; 
x_64 = lean_unbox(x_54);
lean_dec(x_54);
x_57 = x_64;
goto block_61;
}
block_61:
{
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_56);
lean_dec(x_51);
x_58 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_19, x_8, x_4, x_10, x_11, x_12, x_52, x_55);
lean_dec(x_7);
lean_dec(x_6);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
if (lean_is_scalar(x_51)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_51;
}
lean_ctor_set(x_59, 0, x_23);
lean_ctor_set(x_59, 1, x_52);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_51);
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_ctor_set(x_49, 0, x_67);
x_68 = l_Lake_checkHashUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_5, x_6, x_49, x_9, x_12, x_52, x_48);
lean_dec(x_52);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_66);
lean_dec(x_18);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_19, x_8, x_4, x_10, x_11, x_12, x_73, x_72);
lean_dec(x_7);
lean_dec(x_6);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_dec(x_69);
x_77 = lean_box(1);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_76, sizeof(void*)*2);
x_80 = lean_unbox(x_77);
x_81 = l_Lake_JobAction_merge(x_79, x_80);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
x_83 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_81);
x_84 = lean_ctor_get(x_66, 2);
lean_inc(x_84);
lean_dec(x_66);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_array_get_size(x_84);
x_87 = lean_nat_dec_lt(x_85, x_86);
if (x_87 == 0)
{
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_24 = x_83;
x_25 = x_75;
goto block_28;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_86, x_86);
if (x_88 == 0)
{
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_24 = x_83;
x_25 = x_75;
goto block_28;
}
else
{
lean_object* x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_box(0);
x_90 = lean_usize_of_nat(x_85);
x_91 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_92 = l_Array_foldlMUnsafe_fold___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__3(x_84, x_90, x_91, x_89, x_4, x_10, x_11, x_12, x_83, x_75);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_84);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_24 = x_95;
x_25 = x_94;
goto block_28;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_96 = lean_ctor_get(x_49, 0);
lean_inc(x_96);
lean_dec(x_49);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lake_checkHashUpToDate___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__1___redArg(x_5, x_6, x_98, x_9, x_12, x_52, x_48);
lean_dec(x_52);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_96);
lean_dec(x_18);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = l_Lake_buildUnlessUpToDate_x3f_go(x_6, x_7, x_19, x_8, x_4, x_10, x_11, x_12, x_104, x_103);
lean_dec(x_7);
lean_dec(x_6);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
lean_dec(x_100);
x_108 = lean_box(1);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_107, sizeof(void*)*2);
x_111 = lean_unbox(x_108);
x_112 = l_Lake_JobAction_merge(x_110, x_111);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_112);
x_115 = lean_ctor_get(x_96, 2);
lean_inc(x_115);
lean_dec(x_96);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_array_get_size(x_115);
x_118 = lean_nat_dec_lt(x_116, x_117);
if (x_118 == 0)
{
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_24 = x_114;
x_25 = x_106;
goto block_28;
}
else
{
uint8_t x_119; 
x_119 = lean_nat_dec_le(x_117, x_117);
if (x_119 == 0)
{
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_24 = x_114;
x_25 = x_106;
goto block_28;
}
else
{
lean_object* x_120; size_t x_121; size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_box(0);
x_121 = lean_usize_of_nat(x_116);
x_122 = lean_usize_of_nat(x_117);
lean_dec(x_117);
x_123 = l_Array_foldlMUnsafe_fold___at___Lake_buildUnlessUpToDate_x3f___at___Lake_buildFileUnlessUpToDate_x27_spec__0_spec__3(x_115, x_121, x_122, x_120, x_4, x_10, x_11, x_12, x_114, x_106);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_115);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_24 = x_126;
x_25 = x_125;
goto block_28;
}
}
}
}
}
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
if (lean_is_scalar(x_18)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_18;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fetchBuildArchive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_string_hash(x_2);
x_12 = l_Lake_Hash_nil;
x_13 = lean_uint64_mix_hash(x_12, x_11);
x_14 = lean_mk_string_unchecked("trace", 5, 5);
lean_inc(x_3);
x_15 = l_System_FilePath_addExtension(x_3, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("<hash>", 6, 6);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_nat_to_int(x_17);
x_20 = lean_uint32_of_nat(x_17);
x_21 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint32(x_21, sizeof(void*)*1, x_20);
x_22 = lean_box_uint64(x_13);
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_box(2);
x_25 = lean_unbox(x_24);
lean_inc(x_3);
x_26 = l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0(x_2, x_3, x_4, x_5, x_3, x_23, x_15, x_25, x_21, x_6, x_7, x_8, x_9, x_10);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 3);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 6);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_System_FilePath_normalize(x_34);
x_36 = l_Lake_joinRelative(x_32, x_35);
lean_dec(x_35);
x_37 = l_System_FilePath_pathExists(x_36, x_28);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_82; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_31, sizeof(void*)*2);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_82 = lean_unbox(x_30);
lean_dec(x_30);
if (x_82 == 0)
{
lean_free_object(x_37);
lean_dec(x_39);
lean_free_object(x_27);
goto block_81;
}
else
{
uint8_t x_83; 
x_83 = lean_unbox(x_39);
lean_dec(x_39);
if (x_83 == 0)
{
lean_free_object(x_37);
lean_free_object(x_27);
goto block_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_36);
lean_dec(x_3);
x_84 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_84, 0, x_41);
lean_ctor_set(x_84, 1, x_43);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_42);
x_85 = lean_box(0);
lean_ctor_set(x_27, 1, x_84);
lean_ctor_set(x_27, 0, x_85);
lean_ctor_set(x_37, 0, x_27);
return x_37;
}
}
block_81:
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_box(1);
x_45 = lean_unbox(x_44);
x_46 = l_Lake_untar(x_3, x_36, x_45, x_41, x_40);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_unbox(x_24);
x_50 = l_Lake_JobAction_merge(x_42, x_49);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_50);
lean_ctor_set(x_48, 1, x_53);
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_50);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_46, 0, x_57);
return x_46;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_48);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_48, 1);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_43);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_50);
lean_ctor_set(x_48, 1, x_60);
return x_46;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_43);
lean_ctor_set_uint8(x_63, sizeof(void*)*2, x_50);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_46, 0, x_64);
return x_46;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_46, 0);
x_66 = lean_ctor_get(x_46, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_46);
x_67 = lean_unbox(x_24);
x_68 = l_Lake_JobAction_merge(x_42, x_67);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_43);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_68);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_77 = x_65;
} else {
 lean_dec_ref(x_65);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_43);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_68);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_66);
return x_80;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_112; 
x_86 = lean_ctor_get(x_37, 0);
x_87 = lean_ctor_get(x_37, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_37);
x_88 = lean_ctor_get(x_31, 0);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_31, sizeof(void*)*2);
x_90 = lean_ctor_get(x_31, 1);
lean_inc(x_90);
lean_dec(x_31);
x_112 = lean_unbox(x_30);
lean_dec(x_30);
if (x_112 == 0)
{
lean_dec(x_86);
lean_free_object(x_27);
goto block_111;
}
else
{
uint8_t x_113; 
x_113 = lean_unbox(x_86);
lean_dec(x_86);
if (x_113 == 0)
{
lean_free_object(x_27);
goto block_111;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_36);
lean_dec(x_3);
x_114 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_114, 0, x_88);
lean_ctor_set(x_114, 1, x_90);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_89);
x_115 = lean_box(0);
lean_ctor_set(x_27, 1, x_114);
lean_ctor_set(x_27, 0, x_115);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_27);
lean_ctor_set(x_116, 1, x_87);
return x_116;
}
}
block_111:
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; 
x_91 = lean_box(1);
x_92 = lean_unbox(x_91);
x_93 = l_Lake_untar(x_3, x_36, x_92, x_88, x_87);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_unbox(x_24);
x_98 = l_Lake_JobAction_merge(x_89, x_97);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_101 = x_94;
} else {
 lean_dec_ref(x_94);
 x_101 = lean_box(0);
}
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_90);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_98);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
if (lean_is_scalar(x_96)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_96;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_95);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_94, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_94, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_107 = x_94;
} else {
 lean_dec_ref(x_94);
 x_107 = lean_box(0);
}
x_108 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_90);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_98);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_108);
if (lean_is_scalar(x_96)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_96;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_95);
return x_110;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_152; 
x_117 = lean_ctor_get(x_27, 0);
x_118 = lean_ctor_get(x_27, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_27);
x_119 = lean_ctor_get(x_1, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 3);
lean_inc(x_120);
lean_dec(x_1);
x_121 = lean_ctor_get(x_120, 6);
lean_inc(x_121);
lean_dec(x_120);
x_122 = l_System_FilePath_normalize(x_121);
x_123 = l_Lake_joinRelative(x_119, x_122);
lean_dec(x_122);
x_124 = l_System_FilePath_pathExists(x_123, x_28);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_118, 0);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_118, sizeof(void*)*2);
x_130 = lean_ctor_get(x_118, 1);
lean_inc(x_130);
lean_dec(x_118);
x_152 = lean_unbox(x_117);
lean_dec(x_117);
if (x_152 == 0)
{
lean_dec(x_127);
lean_dec(x_125);
goto block_151;
}
else
{
uint8_t x_153; 
x_153 = lean_unbox(x_125);
lean_dec(x_125);
if (x_153 == 0)
{
lean_dec(x_127);
goto block_151;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_123);
lean_dec(x_3);
x_154 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_154, 0, x_128);
lean_ctor_set(x_154, 1, x_130);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_129);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
if (lean_is_scalar(x_127)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_127;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_126);
return x_157;
}
}
block_151:
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_131 = lean_box(1);
x_132 = lean_unbox(x_131);
x_133 = l_Lake_untar(x_3, x_123, x_132, x_128, x_126);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_unbox(x_24);
x_138 = l_Lake_JobAction_merge(x_129, x_137);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_134, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_141 = x_134;
} else {
 lean_dec_ref(x_134);
 x_141 = lean_box(0);
}
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_130);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_138);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_142);
if (lean_is_scalar(x_136)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_136;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_135);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_134, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_134, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_147 = x_134;
} else {
 lean_dec_ref(x_134);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_130);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_138);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_145);
lean_ctor_set(x_149, 1, x_148);
if (lean_is_scalar(x_136)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_136;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_135);
return x_150;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_3);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_26);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_26, 0);
lean_dec(x_159);
x_160 = !lean_is_exclusive(x_27);
if (x_160 == 0)
{
return x_26;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_27, 0);
x_162 = lean_ctor_get(x_27, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_27);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_26, 0, x_163);
return x_26;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_164 = lean_ctor_get(x_26, 1);
lean_inc(x_164);
lean_dec(x_26);
x_165 = lean_ctor_get(x_27, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_27, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_167 = x_27;
} else {
 lean_dec_ref(x_27);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_164);
return x_169;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lake_buildUnlessUpToDate_x3f___at___Lake_Package_fetchBuildArchive_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_box(2);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_11 = lean_unbox(x_8);
x_12 = l_Lake_JobAction_merge(x_10, x_11);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_9);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__2), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_11 = lean_apply_1(x_1, x_2);
x_12 = l_Lake_Package_fetchBuildArchive(x_2, x_4, x_11, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(1);
lean_ctor_set(x_13, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
x_25 = lean_box(1);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_12, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_12, 0, x_33);
return x_12;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_37 = x_13;
} else {
 lean_dec_ref(x_13);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__5), 10, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_12);
lean_closure_set(x_19, 2, x_2);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
x_22 = lean_apply_1(x_3, x_12);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, x_4);
lean_closure_set(x_23, 3, lean_box(0));
lean_closure_set(x_23, 4, lean_box(0));
lean_closure_set(x_23, 5, x_22);
lean_closure_set(x_23, 6, x_19);
x_24 = lean_alloc_closure((void*)(l_Lake_EquipT_tryCatch), 8, 7);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
lean_closure_set(x_24, 2, lean_box(0));
lean_closure_set(x_24, 3, x_5);
lean_closure_set(x_24, 4, lean_box(0));
lean_closure_set(x_24, 5, x_23);
lean_closure_set(x_24, 6, x_6);
x_25 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
lean_closure_set(x_25, 2, x_4);
lean_closure_set(x_25, 3, lean_box(0));
lean_closure_set(x_25, 4, lean_box(0));
lean_closure_set(x_25, 5, x_24);
lean_closure_set(x_25, 6, x_7);
x_26 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_27 = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 11, 5);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_8);
lean_closure_set(x_27, 2, x_25);
lean_closure_set(x_27, 3, x_26);
lean_closure_set(x_27, 4, x_20);
x_28 = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM), 8, 2);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM), 8, 2);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, x_28);
lean_inc(x_16);
x_30 = l_Lake_ensureJob(lean_box(0), x_8, x_29, x_13, x_14, x_15, x_16, x_17, x_18);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_box(1);
x_36 = lean_unbox(x_35);
x_37 = l_Lean_Name_toString(x_21, x_36, x_9);
x_38 = lean_mk_string_unchecked(":", 1, 1);
x_39 = l_Lake_Name_eraseHead(x_10);
x_40 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_41 = lean_unbox(x_35);
x_42 = l_Lean_Name_toString(x_39, x_41, x_11);
x_43 = lean_ctor_get(x_16, 3);
lean_inc(x_43);
lean_dec(x_16);
x_44 = lean_st_ref_take(x_43, x_32);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_string_append(x_40, x_42);
lean_dec(x_42);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_dec(x_34);
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_47);
x_51 = lean_unbox(x_35);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_51);
x_52 = l_Lake_Job_toOpaque___redArg(x_50);
x_53 = lean_array_push(x_45, x_52);
x_54 = lean_st_ref_set(x_43, x_53, x_46);
lean_dec(x_43);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = l_Lake_Job_renew___redArg(x_50);
lean_ctor_set(x_31, 0, x_57);
lean_ctor_set(x_54, 0, x_31);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = l_Lake_Job_renew___redArg(x_50);
lean_ctor_set(x_31, 0, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_31);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_61 = lean_ctor_get(x_31, 0);
x_62 = lean_ctor_get(x_31, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_31);
x_63 = lean_box(1);
x_64 = lean_unbox(x_63);
x_65 = l_Lean_Name_toString(x_21, x_64, x_9);
x_66 = lean_mk_string_unchecked(":", 1, 1);
x_67 = l_Lake_Name_eraseHead(x_10);
x_68 = lean_string_append(x_65, x_66);
lean_dec(x_66);
x_69 = lean_unbox(x_63);
x_70 = l_Lean_Name_toString(x_67, x_69, x_11);
x_71 = lean_ctor_get(x_16, 3);
lean_inc(x_71);
lean_dec(x_16);
x_72 = lean_st_ref_take(x_71, x_32);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_string_append(x_68, x_70);
lean_dec(x_70);
x_76 = lean_ctor_get(x_61, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
lean_dec(x_61);
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_75);
x_79 = lean_unbox(x_63);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_79);
x_80 = l_Lake_Job_toOpaque___redArg(x_78);
x_81 = lean_array_push(x_73, x_80);
x_82 = lean_st_ref_set(x_71, x_81, x_74);
lean_dec(x_71);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = l_Lake_Job_renew___redArg(x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_62);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_5 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 7, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 7, 0);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_8 = l_instToStringBool;
x_9 = lean_alloc_closure((void*)(l_Lean_instToJsonBool___lam__0___boxed), 1, 0);
x_10 = l_Lake_instDataKindBool;
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
lean_inc(x_11);
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
x_23 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_22);
x_24 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 3);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
lean_closure_set(x_25, 2, x_24);
x_26 = l_Lake_EStateT_instMonadExceptOfOfMonad(lean_box(0), lean_box(0), lean_box(0), x_11);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__4___boxed), 4, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3), 5, 1);
lean_closure_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_7);
x_33 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__6___boxed), 18, 11);
lean_closure_set(x_33, 0, x_2);
lean_closure_set(x_33, 1, x_4);
lean_closure_set(x_33, 2, x_3);
lean_closure_set(x_33, 3, x_25);
lean_closure_set(x_33, 4, x_32);
lean_closure_set(x_33, 5, x_6);
lean_closure_set(x_33, 6, x_5);
lean_closure_set(x_33, 7, x_10);
lean_closure_set(x_33, 8, x_7);
lean_closure_set(x_33, 9, x_1);
lean_closure_set(x_33, 10, x_7);
x_34 = l_Lake_Package_keyword;
x_35 = lean_box(1);
x_36 = lean_alloc_closure((void*)(l_Lake_stdFormat___boxed), 5, 3);
lean_closure_set(x_36, 0, lean_box(0));
lean_closure_set(x_36, 1, x_8);
lean_closure_set(x_36, 2, x_9);
x_37 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_10);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_unbox(x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_38);
return x_37;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 7, 0);
x_7 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 7, 0);
x_8 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_9 = l_instToStringBool;
x_10 = lean_alloc_closure((void*)(l_Lean_instToJsonBool___lam__0___boxed), 1, 0);
x_11 = l_Lake_instDataKindBool;
x_12 = l_instMonadEIO(lean_box(0));
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_inc(x_16);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 8, 3);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lake_EStateT_instFunctor___redArg(x_16);
x_19 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, lean_box(0));
lean_inc(x_13);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_13);
x_21 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
x_24 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_23);
x_25 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 3);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, lean_box(0));
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lake_EStateT_instMonadExceptOfOfMonad(lean_box(0), lean_box(0), lean_box(0), x_12);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__4___boxed), 4, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__3), 5, 1);
lean_closure_set(x_29, 0, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_8);
x_34 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__6___boxed), 18, 11);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_4);
lean_closure_set(x_34, 2, x_3);
lean_closure_set(x_34, 3, x_26);
lean_closure_set(x_34, 4, x_33);
lean_closure_set(x_34, 5, x_7);
lean_closure_set(x_34, 6, x_6);
lean_closure_set(x_34, 7, x_11);
lean_closure_set(x_34, 8, x_8);
lean_closure_set(x_34, 9, x_1);
lean_closure_set(x_34, 10, x_8);
x_35 = l_Lake_Package_keyword;
x_36 = lean_box(1);
x_37 = lean_alloc_closure((void*)(l_Lake_stdFormat___boxed), 5, 3);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, x_9);
lean_closure_set(x_37, 2, x_10);
x_38 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_11);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_unbox(x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_39);
return x_38;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__6___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
if (x_4 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_30);
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1 + 3);
x_35 = lean_box(2);
x_36 = lean_unbox(x_35);
x_37 = l_Lake_instDecidableEqVerbosity(x_34, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
x_11 = x_38;
x_12 = x_32;
x_13 = x_10;
goto block_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_box(x_4);
x_40 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed), 2, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_mk_string_unchecked(" (see '", 7, 7);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
lean_inc(x_40);
x_43 = l_Lean_Name_toString(x_42, x_37, x_40);
x_44 = lean_string_append(x_41, x_43);
lean_dec(x_43);
x_45 = lean_mk_string_unchecked(":", 1, 1);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = l_Lake_Name_eraseHead(x_3);
x_48 = l_Lean_Name_toString(x_47, x_37, x_40);
x_49 = lean_string_append(x_46, x_48);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked("' for details)", 14, 14);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_11 = x_51;
x_12 = x_32;
x_13 = x_10;
goto block_28;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_9);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_10);
return x_54;
}
block_28:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_mk_string_unchecked("failed to fetch ", 16, 16);
x_15 = lean_string_append(x_14, x_1);
x_16 = lean_string_append(x_15, x_11);
lean_dec(x_11);
x_17 = lean_box(3);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_19);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
x_22 = lean_array_push(x_20, x_18);
x_23 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(0);
x_12 = lean_mk_string_unchecked("<nil>", 5, 5);
x_13 = l_Lake_BuildTrace_nil(x_12);
x_14 = lean_unbox(x_11);
x_15 = l_Lake_Job_mapM___redArg(x_1, x_3, x_2, x_10, x_14, x_4, x_5, x_6, x_7, x_13, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_inc(x_2);
lean_inc(x_8);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__4___boxed), 10, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_2);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0), 9, 2);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lake_Package_keyword;
x_20 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_2);
x_21 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch), 9, 3);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, lean_box(0));
x_22 = lean_alloc_closure((void*)(l_Lake_EquipT_bind), 8, 7);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, x_4);
lean_closure_set(x_22, 3, lean_box(0));
lean_closure_set(x_22, 4, lean_box(0));
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_16);
lean_inc(x_12);
x_23 = l_Lake_ensureJob(lean_box(0), x_3, x_22, x_9, x_10, x_11, x_12, x_13, x_14);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_Name_toString(x_17, x_29, x_5);
x_31 = lean_mk_string_unchecked(":", 1, 1);
x_32 = l_Lake_Name_eraseHead(x_6);
x_33 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_34 = lean_unbox(x_28);
x_35 = l_Lean_Name_toString(x_32, x_34, x_7);
x_36 = lean_ctor_get(x_12, 3);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_st_ref_take(x_36, x_25);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_string_append(x_33, x_35);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = lean_ctor_get(x_27, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_40);
x_45 = lean_unbox(x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_45);
x_46 = l_Lake_Job_toOpaque___redArg(x_44);
x_47 = lean_array_push(x_38, x_46);
x_48 = lean_st_ref_set(x_36, x_47, x_39);
lean_dec(x_36);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = l_Lake_Job_renew___redArg(x_44);
lean_ctor_set(x_24, 0, x_51);
lean_ctor_set(x_48, 0, x_24);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = l_Lake_Job_renew___redArg(x_44);
lean_ctor_set(x_24, 0, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_55 = lean_ctor_get(x_24, 0);
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_24);
x_57 = lean_box(1);
x_58 = lean_unbox(x_57);
x_59 = l_Lean_Name_toString(x_17, x_58, x_5);
x_60 = lean_mk_string_unchecked(":", 1, 1);
x_61 = l_Lake_Name_eraseHead(x_6);
x_62 = lean_string_append(x_59, x_60);
lean_dec(x_60);
x_63 = lean_unbox(x_57);
x_64 = l_Lean_Name_toString(x_61, x_63, x_7);
x_65 = lean_ctor_get(x_12, 3);
lean_inc(x_65);
lean_dec(x_12);
x_66 = lean_st_ref_take(x_65, x_25);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_string_append(x_62, x_64);
lean_dec(x_64);
x_70 = lean_box(0);
x_71 = lean_ctor_get(x_55, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_55, 1);
lean_inc(x_72);
lean_dec(x_55);
x_73 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_69);
x_74 = lean_unbox(x_70);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_74);
x_75 = l_Lake_Job_toOpaque___redArg(x_73);
x_76 = lean_array_push(x_67, x_75);
x_77 = lean_st_ref_set(x_65, x_76, x_68);
lean_dec(x_65);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = l_Lake_Job_renew___redArg(x_73);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_56);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_4 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_instMonadEIO(lean_box(0));
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_7, 0, x_6);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 8, 3);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lake_EStateT_instFunctor___redArg(x_10);
x_13 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, lean_box(0));
lean_inc(x_7);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 7, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_7);
x_15 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
x_18 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_17);
x_19 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 3);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_19);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 14, 7);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_5);
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_1);
lean_closure_set(x_21, 6, x_4);
x_22 = l_Lake_Package_keyword;
x_23 = lean_box(1);
x_24 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_24, 0, lean_box(0));
x_25 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_26);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_6 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_7 = l_Lake_instDataKindUnit;
x_8 = l_instMonadEIO(lean_box(0));
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_9, 0, x_8);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 8, 3);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
x_14 = l_Lake_EStateT_instFunctor___redArg(x_12);
x_15 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, lean_box(0));
lean_inc(x_9);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 7, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_9);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
x_20 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_19);
x_21 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 3);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, x_21);
lean_inc(x_6);
x_23 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1), 14, 7);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_7);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_6);
lean_closure_set(x_23, 5, x_1);
lean_closure_set(x_23, 6, x_6);
x_24 = l_Lake_Package_keyword;
x_25 = lean_box(1);
x_26 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_26, 0, lean_box(0));
x_27 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_7);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_unbox(x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_28);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__4(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
if (x_3 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_28);
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1 + 3);
x_33 = lean_box(2);
x_34 = lean_unbox(x_33);
x_35 = l_Lake_instDecidableEqVerbosity(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
x_10 = x_36;
x_11 = x_30;
x_12 = x_9;
goto block_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_box(x_3);
x_38 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_mk_string_unchecked(" (see '", 7, 7);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
lean_inc(x_38);
x_41 = l_Lean_Name_toString(x_40, x_35, x_38);
x_42 = lean_string_append(x_39, x_41);
lean_dec(x_41);
x_43 = lean_mk_string_unchecked(":", 1, 1);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = l_Lake_Name_eraseHead(x_2);
x_46 = l_Lean_Name_toString(x_45, x_35, x_38);
x_47 = lean_string_append(x_44, x_46);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("' for details)", 14, 14);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_10 = x_49;
x_11 = x_30;
x_12 = x_9;
goto block_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_8);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_9);
return x_52;
}
block_26:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_mk_string_unchecked("failed to fetch build cache", 27, 27);
x_14 = lean_string_append(x_13, x_10);
lean_dec(x_10);
x_15 = lean_box(3);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
x_20 = lean_array_push(x_18, x_16);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_box(0);
x_16 = lean_mk_string_unchecked("<nil>", 5, 5);
x_17 = l_Lake_BuildTrace_nil(x_16);
x_18 = lean_unbox(x_15);
x_19 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_13, x_2, x_14, x_18, x_3, x_4, x_5, x_6, x_17, x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_10, 0, x_21);
lean_ctor_set(x_19, 0, x_10);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_10, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_box(0);
x_29 = lean_mk_string_unchecked("<nil>", 5, 5);
x_30 = l_Lake_BuildTrace_nil(x_29);
x_31 = lean_unbox(x_28);
x_32 = l_Lake_Job_mapM___at___Lake_Package_maybeFetchBuildCacheWithWarning_spec__0___redArg(x_25, x_2, x_27, x_31, x_3, x_4, x_5, x_6, x_30, x_11);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
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
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_26);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_9, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_9, 0, x_43);
return x_9;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_dec(x_9);
x_45 = lean_ctor_get(x_10, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_47 = x_10;
} else {
 lean_dec_ref(x_10);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__4___boxed), 9, 2);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lake_Package_keyword;
x_16 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 8, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_12);
lean_inc(x_9);
x_18 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(x_17, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Name_toString(x_13, x_24, x_2);
x_26 = lean_mk_string_unchecked(":", 1, 1);
x_27 = l_Lake_Name_eraseHead(x_3);
x_28 = lean_ctor_get(x_9, 3);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_st_ref_take(x_28, x_20);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_33 = lean_unbox(x_23);
x_34 = l_Lean_Name_toString(x_27, x_33, x_4);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_unbox(x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_40);
x_41 = l_Lake_Job_toOpaque___redArg(x_39);
x_42 = lean_array_push(x_30, x_41);
x_43 = lean_st_ref_set(x_28, x_42, x_31);
lean_dec(x_28);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_19, 0, x_46);
lean_ctor_set(x_43, 0, x_19);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_19, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
x_54 = l_Lean_Name_toString(x_13, x_53, x_2);
x_55 = lean_mk_string_unchecked(":", 1, 1);
x_56 = l_Lake_Name_eraseHead(x_3);
x_57 = lean_ctor_get(x_9, 3);
lean_inc(x_57);
lean_dec(x_9);
x_58 = lean_st_ref_take(x_57, x_20);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_62 = lean_unbox(x_52);
x_63 = l_Lean_Name_toString(x_56, x_62, x_4);
x_64 = lean_string_append(x_61, x_63);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = lean_ctor_get(x_50, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_dec(x_50);
x_68 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_64);
x_69 = lean_unbox(x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_69);
x_70 = l_Lake_Job_toOpaque___redArg(x_68);
x_71 = lean_array_push(x_59, x_70);
x_72 = lean_st_ref_set(x_57, x_71, x_60);
lean_dec(x_57);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = l_Lake_Job_renew___redArg(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_51);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_2 = l_Lake_Package_buildCacheFacet;
x_3 = l_Lake_Package_optBuildCacheFacet;
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1), 11, 4);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, x_1);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = lean_box(1);
x_8 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_8, 0, lean_box(0));
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_10);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Package_buildCacheFacetConfig___lam__4(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_Package_recFetchDeps_spec__2_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l_Lake_instDataKindBool;
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
x_103 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_39, x_101, x_2, x_3, x_4, x_5, x_102, x_12);
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
x_105 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_39, x_104, x_2, x_3, x_4, x_5, x_37, x_12);
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
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
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
x_63 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
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
x_79 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__0), 2, 1);
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
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_29; lean_object* x_30; 
lean_inc(x_7);
lean_inc(x_1);
x_29 = l_Lake_Package_getBarrelUrl___redArg(x_1, x_7, x_8, x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = l_Lake_defaultLakeDir;
x_36 = l_Lake_joinRelative(x_34, x_35);
x_37 = lean_mk_string_unchecked("build.barrel", 12, 12);
x_38 = l_Lake_joinRelative(x_36, x_37);
lean_dec(x_37);
x_39 = l_Lake_Package_fetchBuildArchive(x_1, x_32, x_38, x_2, x_4, x_5, x_6, x_7, x_33, x_31);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_10 = x_3;
x_11 = x_42;
x_12 = x_41;
goto block_16;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_17 = x_44;
x_18 = x_43;
goto block_28;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_dec(x_29);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_dec(x_30);
x_17 = x_46;
x_18 = x_45;
goto block_28;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
block_28:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_box(2);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
x_22 = lean_unbox(x_19);
x_23 = l_Lake_JobAction_merge(x_21, x_22);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_10 = x_27;
x_11 = x_25;
x_12 = x_18;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_string_utf8_byte_size(x_15);
x_18 = l_instDecidableEqPos(x_17, x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_19 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_20 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_15, x_17, x_8);
x_21 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_15, x_20, x_17);
x_22 = lean_string_utf8_extract(x_15, x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
x_23 = lean_string_append(x_19, x_22);
lean_dec(x_22);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
x_28 = lean_box(0);
x_29 = lean_array_push(x_27, x_25);
x_30 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_30);
x_33 = lean_unbox(x_16);
lean_dec(x_16);
x_34 = l_Lake_Package_optBarrelFacetConfig___lam__0(x_33, x_28, x_3, x_4, x_5, x_6, x_32, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_8);
x_35 = lean_box(0);
x_36 = lean_unbox(x_16);
lean_dec(x_16);
x_37 = l_Lake_Package_optBarrelFacetConfig___lam__0(x_36, x_35, x_3, x_4, x_5, x_6, x_14, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_10);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_10, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_10, 0, x_43);
return x_10;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_dec(x_10);
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_47 = x_11;
} else {
 lean_dec_ref(x_11);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_mk_empty_array_with_capacity(x_1);
x_13 = lean_box(0);
x_14 = lean_mk_string_unchecked("<nil>", 5, 5);
x_15 = l_Lake_BuildTrace_nil(x_14);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unbox(x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_17);
x_18 = lean_box(x_3);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 9, 8);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_6);
lean_closure_set(x_19, 3, x_7);
lean_closure_set(x_19, 4, x_8);
lean_closure_set(x_19, 5, x_9);
lean_closure_set(x_19, 6, x_16);
lean_closure_set(x_19, 7, x_1);
x_20 = lean_io_as_task(x_19, x_1, x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
x_25 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_10);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_5);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_10);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_mk_string_unchecked("", 0, 0);
x_14 = lean_box(1);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__3___boxed), 9, 3);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 5);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_14);
lean_closure_set(x_17, 3, x_2);
lean_closure_set(x_17, 4, x_13);
lean_inc(x_10);
x_18 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(x_17, x_7, x_8, x_9, x_10, x_11, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_unbox(x_14);
x_25 = l_Lean_Name_toString(x_23, x_24, x_3);
x_26 = lean_mk_string_unchecked(":", 1, 1);
x_27 = l_Lake_Name_eraseHead(x_4);
x_28 = lean_ctor_get(x_10, 3);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_st_ref_take(x_28, x_20);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_33 = lean_unbox(x_14);
x_34 = l_Lean_Name_toString(x_27, x_33, x_5);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
x_39 = lean_unbox(x_14);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_39);
x_40 = l_Lake_Job_toOpaque___redArg(x_38);
x_41 = lean_array_push(x_30, x_40);
x_42 = lean_st_ref_set(x_28, x_41, x_31);
lean_dec(x_28);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lake_Job_renew___redArg(x_38);
lean_ctor_set(x_19, 0, x_45);
lean_ctor_set(x_42, 0, x_19);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lake_Job_renew___redArg(x_38);
lean_ctor_set(x_19, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_ctor_get(x_6, 0);
lean_inc(x_51);
lean_dec(x_6);
x_52 = lean_unbox(x_14);
x_53 = l_Lean_Name_toString(x_51, x_52, x_3);
x_54 = lean_mk_string_unchecked(":", 1, 1);
x_55 = l_Lake_Name_eraseHead(x_4);
x_56 = lean_ctor_get(x_10, 3);
lean_inc(x_56);
lean_dec(x_10);
x_57 = lean_st_ref_take(x_56, x_20);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_61 = lean_unbox(x_14);
x_62 = l_Lean_Name_toString(x_55, x_61, x_5);
x_63 = lean_string_append(x_60, x_62);
lean_dec(x_62);
x_64 = lean_ctor_get(x_49, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_dec(x_49);
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_63);
x_67 = lean_unbox(x_14);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_67);
x_68 = l_Lake_Job_toOpaque___redArg(x_66);
x_69 = lean_array_push(x_58, x_68);
x_70 = lean_st_ref_set(x_56, x_69, x_59);
lean_dec(x_56);
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
x_73 = l_Lake_Job_renew___redArg(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_50);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_3 = l_Lake_Package_optReservoirBarrelFacet;
x_4 = l_Lake_Reservoir_lakeHeaders;
x_5 = l_Lake_instDataKindBool;
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__4), 12, 5);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_2);
x_7 = l_Lake_Package_keyword;
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_1);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_10);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Package_optBarrelFacetConfig___lam__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lake_Package_optBarrelFacetConfig___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_Package_optBarrelFacetConfig___lam__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lake_Package_optBarrelFacetConfig___lam__2(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
if (x_3 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_28);
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1 + 3);
x_33 = lean_box(2);
x_34 = lean_unbox(x_33);
x_35 = l_Lake_instDecidableEqVerbosity(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
x_10 = x_36;
x_11 = x_30;
x_12 = x_9;
goto block_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_box(x_3);
x_38 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_mk_string_unchecked(" (see '", 7, 7);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
lean_inc(x_38);
x_41 = l_Lean_Name_toString(x_40, x_35, x_38);
x_42 = lean_string_append(x_39, x_41);
lean_dec(x_41);
x_43 = lean_mk_string_unchecked(":", 1, 1);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = l_Lake_Name_eraseHead(x_2);
x_46 = l_Lean_Name_toString(x_45, x_35, x_38);
x_47 = lean_string_append(x_44, x_46);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("' for details)", 14, 14);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_10 = x_49;
x_11 = x_30;
x_12 = x_9;
goto block_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_8);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_9);
return x_52;
}
block_26:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_mk_string_unchecked("failed to fetch Reservoir build", 31, 31);
x_14 = lean_string_append(x_13, x_10);
lean_dec(x_10);
x_15 = lean_box(3);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
x_20 = lean_array_push(x_18, x_16);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__4___boxed), 9, 2);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lake_Package_keyword;
x_16 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 8, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_12);
lean_inc(x_9);
x_18 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(x_17, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Name_toString(x_13, x_24, x_2);
x_26 = lean_mk_string_unchecked(":", 1, 1);
x_27 = l_Lake_Name_eraseHead(x_3);
x_28 = lean_ctor_get(x_9, 3);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_st_ref_take(x_28, x_20);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_33 = lean_unbox(x_23);
x_34 = l_Lean_Name_toString(x_27, x_33, x_4);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_unbox(x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_40);
x_41 = l_Lake_Job_toOpaque___redArg(x_39);
x_42 = lean_array_push(x_30, x_41);
x_43 = lean_st_ref_set(x_28, x_42, x_31);
lean_dec(x_28);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_19, 0, x_46);
lean_ctor_set(x_43, 0, x_19);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_19, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
x_54 = l_Lean_Name_toString(x_13, x_53, x_2);
x_55 = lean_mk_string_unchecked(":", 1, 1);
x_56 = l_Lake_Name_eraseHead(x_3);
x_57 = lean_ctor_get(x_9, 3);
lean_inc(x_57);
lean_dec(x_9);
x_58 = lean_st_ref_take(x_57, x_20);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_62 = lean_unbox(x_52);
x_63 = l_Lean_Name_toString(x_56, x_62, x_4);
x_64 = lean_string_append(x_61, x_63);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = lean_ctor_get(x_50, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_dec(x_50);
x_68 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_64);
x_69 = lean_unbox(x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_69);
x_70 = l_Lake_Job_toOpaque___redArg(x_68);
x_71 = lean_array_push(x_59, x_70);
x_72 = lean_st_ref_set(x_57, x_71, x_60);
lean_dec(x_57);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = l_Lake_Job_renew___redArg(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_51);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_2 = l_Lake_Package_reservoirBarrelFacet;
x_3 = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1), 11, 4);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, x_1);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = lean_box(1);
x_8 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_8, 0, lean_box(0));
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_10);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Package_barrelFacetConfig___lam__4(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_29; lean_object* x_30; 
lean_inc(x_1);
x_29 = l_Lake_Package_getReleaseUrl___redArg(x_1, x_8, x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = l_Lake_defaultLakeDir;
x_36 = l_Lake_joinRelative(x_34, x_35);
x_37 = lean_ctor_get(x_1, 16);
lean_inc(x_37);
x_38 = l_Lake_joinRelative(x_36, x_37);
lean_dec(x_37);
x_39 = l_Lake_Package_fetchBuildArchive(x_1, x_32, x_38, x_2, x_4, x_5, x_6, x_7, x_33, x_31);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_10 = x_3;
x_11 = x_42;
x_12 = x_41;
goto block_16;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_17 = x_44;
x_18 = x_43;
goto block_28;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_dec(x_29);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_dec(x_30);
x_17 = x_46;
x_18 = x_45;
goto block_28;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
block_28:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_box(2);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
x_22 = lean_unbox(x_19);
x_23 = l_Lake_JobAction_merge(x_21, x_22);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_10 = x_27;
x_11 = x_25;
x_12 = x_18;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = lean_box(1);
lean_inc(x_7);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__3___boxed), 9, 3);
lean_closure_set(x_16, 0, x_7);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 5);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_14);
lean_inc(x_11);
x_18 = l_Lake_ensureJob___at___Lake_Package_optBarrelFacetConfig_spec__0(x_17, x_8, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_unbox(x_15);
x_25 = l_Lean_Name_toString(x_23, x_24, x_4);
x_26 = lean_mk_string_unchecked(":", 1, 1);
x_27 = l_Lake_Name_eraseHead(x_5);
x_28 = lean_ctor_get(x_11, 3);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_st_ref_take(x_28, x_20);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_33 = lean_unbox(x_15);
x_34 = l_Lean_Name_toString(x_27, x_33, x_6);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
x_39 = lean_unbox(x_15);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_39);
x_40 = l_Lake_Job_toOpaque___redArg(x_38);
x_41 = lean_array_push(x_30, x_40);
x_42 = lean_st_ref_set(x_28, x_41, x_31);
lean_dec(x_28);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lake_Job_renew___redArg(x_38);
lean_ctor_set(x_19, 0, x_45);
lean_ctor_set(x_42, 0, x_19);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lake_Job_renew___redArg(x_38);
lean_ctor_set(x_19, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_ctor_get(x_7, 0);
lean_inc(x_51);
lean_dec(x_7);
x_52 = lean_unbox(x_15);
x_53 = l_Lean_Name_toString(x_51, x_52, x_4);
x_54 = lean_mk_string_unchecked(":", 1, 1);
x_55 = l_Lake_Name_eraseHead(x_5);
x_56 = lean_ctor_get(x_11, 3);
lean_inc(x_56);
lean_dec(x_11);
x_57 = lean_st_ref_take(x_56, x_20);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_61 = lean_unbox(x_15);
x_62 = l_Lean_Name_toString(x_55, x_61, x_6);
x_63 = lean_string_append(x_60, x_62);
lean_dec(x_62);
x_64 = lean_ctor_get(x_49, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_dec(x_49);
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_63);
x_67 = lean_unbox(x_15);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_67);
x_68 = l_Lake_Job_toOpaque___redArg(x_66);
x_69 = lean_array_push(x_58, x_68);
x_70 = lean_st_ref_set(x_56, x_69, x_59);
lean_dec(x_56);
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
x_73 = l_Lake_Job_renew___redArg(x_66);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_50);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_optBuildCacheFacetConfig___lam__1___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_3 = l_Lake_Package_optGitHubReleaseFacet;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = l_Lake_instDataKindBool;
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__4), 13, 6);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_2);
lean_closure_set(x_7, 4, x_3);
lean_closure_set(x_7, 5, x_2);
x_8 = l_Lake_Package_keyword;
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_1);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_11);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Package_optGitHubReleaseFacetConfig___lam__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lake_Package_optReleaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optGitHubReleaseFacetConfig;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
if (x_3 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_28);
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1 + 3);
x_33 = lean_box(2);
x_34 = lean_unbox(x_33);
x_35 = l_Lake_instDecidableEqVerbosity(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked(" (run with '-v' for details)", 28, 28);
x_10 = x_36;
x_11 = x_30;
x_12 = x_9;
goto block_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_box(x_3);
x_38 = lean_alloc_closure((void*)(l_Lake_Package_maybeFetchBuildCacheWithWarning___lam__2___boxed), 2, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_mk_string_unchecked(" (see '", 7, 7);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
lean_inc(x_38);
x_41 = l_Lean_Name_toString(x_40, x_35, x_38);
x_42 = lean_string_append(x_39, x_41);
lean_dec(x_41);
x_43 = lean_mk_string_unchecked(":", 1, 1);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = l_Lake_Name_eraseHead(x_2);
x_46 = l_Lean_Name_toString(x_45, x_35, x_38);
x_47 = lean_string_append(x_44, x_46);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("' for details)", 14, 14);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_10 = x_49;
x_11 = x_30;
x_12 = x_9;
goto block_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_8);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_9);
return x_52;
}
block_26:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_mk_string_unchecked("failed to fetch GitHub release", 30, 30);
x_14 = lean_string_append(x_13, x_10);
lean_dec(x_10);
x_15 = lean_box(3);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
x_20 = lean_array_push(x_18, x_16);
x_21 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__4___boxed), 9, 2);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lake_Package_keyword;
x_16 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_1);
x_17 = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__0), 8, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_12);
lean_inc(x_9);
x_18 = l_Lake_ensureJob___at___Lake_Package_recBuildExtraDepTargets_spec__1(x_17, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Name_toString(x_13, x_24, x_2);
x_26 = lean_mk_string_unchecked(":", 1, 1);
x_27 = l_Lake_Name_eraseHead(x_3);
x_28 = lean_ctor_get(x_9, 3);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_st_ref_take(x_28, x_20);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_33 = lean_unbox(x_23);
x_34 = l_Lean_Name_toString(x_27, x_33, x_4);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_unbox(x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_40);
x_41 = l_Lake_Job_toOpaque___redArg(x_39);
x_42 = lean_array_push(x_30, x_41);
x_43 = lean_st_ref_set(x_28, x_42, x_31);
lean_dec(x_28);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_19, 0, x_46);
lean_ctor_set(x_43, 0, x_19);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l_Lake_Job_renew___redArg(x_39);
lean_ctor_set(x_19, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
x_54 = l_Lean_Name_toString(x_13, x_53, x_2);
x_55 = lean_mk_string_unchecked(":", 1, 1);
x_56 = l_Lake_Name_eraseHead(x_3);
x_57 = lean_ctor_get(x_9, 3);
lean_inc(x_57);
lean_dec(x_9);
x_58 = lean_st_ref_take(x_57, x_20);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_62 = lean_unbox(x_52);
x_63 = l_Lean_Name_toString(x_56, x_62, x_4);
x_64 = lean_string_append(x_61, x_63);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = lean_ctor_get(x_50, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_dec(x_50);
x_68 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_64);
x_69 = lean_unbox(x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_69);
x_70 = l_Lake_Job_toOpaque___redArg(x_68);
x_71 = lean_array_push(x_59, x_70);
x_72 = lean_st_ref_set(x_57, x_71, x_60);
lean_dec(x_57);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = l_Lake_Job_renew___redArg(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_51);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___lam__0___boxed), 1, 0);
x_2 = l_Lake_Package_gitHubReleaseFacet;
x_3 = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1), 11, 4);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, x_1);
x_5 = l_Lake_instDataKindUnit;
x_6 = l_Lake_Package_keyword;
x_7 = lean_box(1);
x_8 = lean_alloc_closure((void*)(l_Lake_nullFormat___boxed), 3, 1);
lean_closure_set(x_8, 0, lean_box(0));
x_9 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_10);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_Package_gitHubReleaseFacetConfig___lam__4(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l_Lake_Package_releaseFacetConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_gitHubReleaseFacetConfig;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lake_JobState_merge(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_11);
x_12 = l_Lake_JobState_merge(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
lean_dec(x_12);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_nat_add(x_22, x_19);
lean_dec(x_19);
lean_dec(x_22);
lean_inc(x_20);
x_24 = l_Lake_JobState_merge(x_1, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
lean_dec(x_24);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_23);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_array_get_size(x_31);
lean_dec(x_31);
x_33 = lean_nat_add(x_32, x_29);
lean_dec(x_29);
lean_dec(x_32);
lean_inc(x_30);
x_34 = l_Lake_JobState_merge(x_1, x_30);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_34, sizeof(void*)*2);
lean_dec(x_34);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = l_Lake_BuildTrace_mix(x_1, x_19);
x_21 = lean_apply_1(x_2, x_17);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = lean_box(1);
x_45 = lean_unbox(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_21, x_45, x_3, x_4, x_5, x_6, x_24, x_9);
lean_dec(x_24);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_string_utf8_byte_size(x_51);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_instDecidableEqPos(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_56 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_57 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_51, x_53, x_54);
x_58 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_51, x_57, x_53);
x_59 = lean_string_utf8_extract(x_51, x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_51);
x_60 = lean_string_append(x_56, x_59);
lean_dec(x_59);
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
x_65 = lean_box(0);
x_66 = lean_array_push(x_64, x_62);
x_67 = lean_ctor_get_uint8(x_50, sizeof(void*)*2);
x_68 = lean_ctor_get(x_50, 1);
lean_inc(x_68);
lean_dec(x_50);
x_69 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_67);
x_70 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_52, x_65, x_3, x_4, x_5, x_6, x_69, x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = x_70;
goto block_44;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_53);
lean_dec(x_51);
x_71 = lean_box(0);
x_72 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_52, x_71, x_3, x_4, x_5, x_6, x_50, x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = x_72;
goto block_44;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = lean_ctor_get(x_46, 1);
lean_inc(x_73);
lean_dec(x_46);
x_74 = lean_ctor_get(x_47, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_dec(x_47);
x_10 = x_74;
x_11 = x_75;
x_12 = x_73;
goto block_16;
}
block_44:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_unbox(x_25);
x_34 = lean_task_map(x_31, x_32, x_7, x_33);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_unbox(x_25);
x_42 = lean_task_map(x_39, x_40, x_7, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_8);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_task_pure(x_8);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_9);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_8, 0);
x_80 = lean_ctor_get(x_8, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_8);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_task_pure(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_9);
return x_83;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_task_pure(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__2), 9, 7);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_6);
lean_closure_set(x_11, 4, x_7);
lean_closure_set(x_11, 5, x_8);
lean_closure_set(x_11, 6, x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_io_bind_task(x_12, x_11, x_3, x_4, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_mk_string_unchecked("<nil>", 5, 5);
x_10 = l_Lake_BuildTrace_nil(x_9);
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
x_14 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_13, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_instDecidableNot___redArg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_mk_string_unchecked("<nil>", 5, 5);
x_17 = l_Lake_BuildTrace_nil(x_16);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unbox(x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_19);
x_20 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_18, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_21, 1, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_34 = x_21;
} else {
 lean_dec_ref(x_21);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_20, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_21, 1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_ctor_set(x_21, 1, x_42);
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_20, 0, x_46);
return x_20;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_dec(x_20);
x_48 = lean_ctor_get(x_21, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_50 = x_21;
} else {
 lean_dec_ref(x_21);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_54 = l_Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_59, 0, x_2);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_box(0);
x_62 = lean_mk_string_unchecked("<nil>", 5, 5);
x_63 = l_Lake_BuildTrace_nil(x_62);
x_64 = lean_unbox(x_61);
x_65 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_58, x_59, x_60, x_64, x_3, x_4, x_5, x_6, x_63, x_56);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_ctor_set(x_55, 0, x_67);
lean_ctor_set(x_65, 0, x_55);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_65);
lean_ctor_set(x_55, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_ctor_get(x_55, 0);
x_72 = lean_ctor_get(x_55, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_55);
x_73 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_73, 0, x_2);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_box(0);
x_76 = lean_mk_string_unchecked("<nil>", 5, 5);
x_77 = l_Lake_BuildTrace_nil(x_76);
x_78 = lean_unbox(x_75);
x_79 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_71, x_73, x_74, x_78, x_3, x_4, x_5, x_6, x_77, x_56);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_72);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_54);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_54, 0);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_55);
if (x_87 == 0)
{
return x_54;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_55, 0);
x_89 = lean_ctor_get(x_55, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_55);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_54, 0, x_90);
return x_54;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_54, 1);
lean_inc(x_91);
lean_dec(x_54);
x_92 = lean_ctor_get(x_55, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_55, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_94 = x_55;
} else {
 lean_dec_ref(x_55);
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
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_afterBuildCacheAsync___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lake_Job_bindM___at___Lake_Package_afterBuildCacheAsync_spec__0(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_afterBuildCacheAsync___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_afterBuildCacheAsync___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = l_Lake_BuildTrace_mix(x_1, x_11);
x_13 = lean_apply_1(x_2, x_9);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_15);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_13, x_18, x_3, x_4, x_5, x_6, x_16, x_8);
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_string_utf8_byte_size(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_instDecidableEqPos(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_30 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_24, x_26, x_27);
x_31 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_24, x_30, x_26);
x_32 = lean_string_utf8_extract(x_24, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_24);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
x_38 = lean_box(0);
x_39 = lean_array_push(x_37, x_35);
x_40 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_40);
x_43 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(x_25, x_38, x_3, x_4, x_5, x_6, x_42, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_26);
lean_dec(x_24);
x_44 = lean_box(0);
x_45 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(x_25, x_44, x_3, x_4, x_5, x_6, x_23, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_19, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_19, 0, x_51);
return x_19;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
lean_dec(x_19);
x_53 = lean_ctor_get(x_20, 0);
lean_inc(x_53);
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
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_7);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_7);
lean_ctor_set(x_59, 1, x_8);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_7, 0);
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_7);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_8);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_alloc_closure((void*)(l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__1), 8, 6);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_6);
lean_closure_set(x_11, 4, x_7);
lean_closure_set(x_11, 5, x_8);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_io_map_task(x_11, x_12, x_3, x_4, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_inputBinFile_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_16 = x_11;
} else {
 lean_dec_ref(x_11);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_24 = lean_string_utf8_byte_size(x_17);
x_25 = l_instDecidableEqPos(x_24, x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_27 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_17, x_24, x_8);
x_28 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_17, x_27, x_24);
x_29 = lean_string_utf8_extract(x_17, x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
x_30 = lean_string_append(x_26, x_29);
lean_dec(x_29);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
x_35 = lean_array_push(x_34, x_32);
x_36 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_36);
x_19 = x_38;
x_20 = x_13;
goto block_23;
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_8);
x_19 = x_15;
x_20 = x_13;
goto block_23;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
if (lean_is_scalar(x_16)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_16;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_14)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_14;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_10, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_10, 0, x_44);
return x_10;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_dec(x_10);
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_48 = x_11;
} else {
 lean_dec_ref(x_11);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_mk_string_unchecked("<nil>", 5, 5);
x_10 = l_Lake_BuildTrace_nil(x_9);
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
x_14 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_13, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_instDecidableNot___redArg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_box(0);
x_18 = lean_mk_string_unchecked("<nil>", 5, 5);
x_19 = l_Lake_BuildTrace_nil(x_18);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_unbox(x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_21);
x_22 = lean_box(1);
x_23 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 8);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_20);
lean_closure_set(x_23, 7, x_15);
x_24 = lean_io_as_task(x_23, x_15, x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
lean_ctor_set(x_24, 0, x_30);
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_34 = lean_mk_string_unchecked("", 0, 0);
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_14);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_7);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_38 = l_Lake_Package_maybeFetchBuildCache(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed), 8, 1);
lean_closure_set(x_43, 0, x_2);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_box(0);
x_46 = lean_mk_string_unchecked("<nil>", 5, 5);
x_47 = l_Lake_BuildTrace_nil(x_46);
x_48 = lean_unbox(x_45);
x_49 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_42, x_43, x_44, x_48, x_3, x_4, x_5, x_6, x_47, x_40);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_ctor_set(x_39, 0, x_51);
lean_ctor_set(x_49, 0, x_39);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set(x_39, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get(x_39, 0);
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_39);
x_57 = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed), 8, 1);
lean_closure_set(x_57, 0, x_2);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_box(0);
x_60 = lean_mk_string_unchecked("<nil>", 5, 5);
x_61 = l_Lake_BuildTrace_nil(x_60);
x_62 = lean_unbox(x_59);
x_63 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_55, x_57, x_58, x_62, x_3, x_4, x_5, x_6, x_61, x_40);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_56);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_38);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_38, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_39);
if (x_71 == 0)
{
return x_38;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 0);
x_73 = lean_ctor_get(x_39, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_39);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_38, 0, x_74);
return x_38;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
lean_dec(x_38);
x_76 = lean_ctor_get(x_39, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_78 = x_39;
} else {
 lean_dec_ref(x_39);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_afterBuildCacheSync___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lake_Job_mapM___at___Lake_Package_afterBuildCacheSync_spec__0(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Package_afterBuildCacheSync___redArg___lam__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_Package_afterBuildCacheSync___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterReleaseSync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Package_afterBuildCacheSync___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_depsFacet;
x_3 = l_Lake_Package_depsFacetConfig;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_2, x_3);
x_5 = l_Lake_Package_transDepsFacet;
x_6 = l_Lake_Package_transDepsFacetConfig;
x_7 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_5, x_6);
x_8 = l_Lake_Package_extraDepFacet;
x_9 = l_Lake_Package_extraDepFacetConfig;
x_10 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_7, x_8, x_9);
x_11 = l_Lake_Package_optBuildCacheFacet;
x_12 = l_Lake_Package_optBuildCacheFacetConfig;
x_13 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_10, x_11, x_12);
x_14 = l_Lake_Package_buildCacheFacet;
x_15 = l_Lake_Package_buildCacheFacetConfig;
x_16 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_13, x_14, x_15);
x_17 = l_Lake_Package_optReservoirBarrelFacet;
x_18 = l_Lake_Package_optBarrelFacetConfig;
x_19 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_16, x_17, x_18);
x_20 = l_Lake_Package_reservoirBarrelFacet;
x_21 = l_Lake_Package_barrelFacetConfig;
x_22 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_19, x_20, x_21);
x_23 = l_Lake_Package_optGitHubReleaseFacet;
x_24 = l_Lake_Package_optGitHubReleaseFacetConfig;
x_25 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_22, x_23, x_24);
x_26 = l_Lake_Package_gitHubReleaseFacet;
x_27 = l_Lake_Package_gitHubReleaseFacetConfig;
x_28 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_25, x_26, x_27);
return x_28;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_initFacetConfigs;
return x_1;
}
}
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Sugar(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Topological(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Reservoir(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Sugar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Topological(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
lean_mark_persistent(l_Lake_Package_depsFacetConfig);
l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7 = _init_l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___Lake_Package_recComputeTransDeps_spec__7);
l_Lake_Package_transDepsFacetConfig = _init_l_Lake_Package_transDepsFacetConfig();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig);
l_Lake_Package_optBuildCacheFacetConfig = _init_l_Lake_Package_optBuildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig);
l_Lake_Package_extraDepFacetConfig = _init_l_Lake_Package_extraDepFacetConfig();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig);
l_Lake_Package_buildCacheFacetConfig = _init_l_Lake_Package_buildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig);
l_Lake_Package_optBarrelFacetConfig = _init_l_Lake_Package_optBarrelFacetConfig();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig);
l_Lake_Package_barrelFacetConfig = _init_l_Lake_Package_barrelFacetConfig();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig);
l_Lake_Package_optGitHubReleaseFacetConfig = _init_l_Lake_Package_optGitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig);
l_Lake_Package_optReleaseFacetConfig = _init_l_Lake_Package_optReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optReleaseFacetConfig);
l_Lake_Package_gitHubReleaseFacetConfig = _init_l_Lake_Package_gitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig);
l_Lake_Package_releaseFacetConfig = _init_l_Lake_Package_releaseFacetConfig();
lean_mark_persistent(l_Lake_Package_releaseFacetConfig);
l_Lake_Package_initFacetConfigs = _init_l_Lake_Package_initFacetConfigs();
lean_mark_persistent(l_Lake_Package_initFacetConfigs);
l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
lean_mark_persistent(l_Lake_initPackageFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
