// Lean compiler output
// Module: Lean.CoreM
// Imports: Lean.Util.RecDepth Lean.Util.Trace Lean.Log Lean.ResolveName Lean.Elab.InfoTree.Types Lean.MonadEnv Lean.Elab.Exception Lean.Language.Basic
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
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_CoreM___hyg_4116_;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantVal_instantiateTypeLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
double lean_float_div(double, double);
lean_object* lean_io_get_tid(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_IO_CancelToken_isSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM;
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isRealizing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLiftIOCoreM;
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937_(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
lean_object* l_EStateM_throw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986_(lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_lcnf_compile_decls(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1(lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_IO_addHeartbeats(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_CoreM___hyg_3975_;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_async;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDeclsOld___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionCoreM;
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_EStateM_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_compileDecls_doCompile___lam__0(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDiag___boxed(lean_object*);
extern lean_object* l_Lean_warningAsError;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM;
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_instantiateValueLevelParams_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_PromiseCheckedResult_commitChecked(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDeclsNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Core_throwMaxHeartbeat___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instBEqInternalExceptionId;
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lam__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueNat;
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_promiseChecked(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263_(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM;
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_stderrAsMessages;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_diagnostics_threshold;
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isRuntime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(uint8_t, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg;
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwInterruptException___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_supportedRecursors;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_inServer;
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instAddMessageContextCoreM;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_debug_moduleNameAtTimeout;
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCache;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_interruptExceptionId;
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_nonBacktrackable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_maxHeartbeats;
LEAN_EXPORT lean_object* l_Lean_internal_cmdlineSnapshots;
lean_object* l_Lean_MessageLog_markAllReported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compiler_enableNew;
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
uint8_t l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("diagnostics", 11, 11);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("collect diagnostic information", 30, 30);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = l_Lean_Name_mkStr2(x_7, x_2);
x_9 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_3, x_6, x_8, x_1);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_mk_string_unchecked("diagnostics", 11, 11);
x_3 = lean_mk_string_unchecked("threshold", 9, 9);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(20u);
x_6 = lean_mk_string_unchecked("only diagnostic counters above this threshold are reported by the definitional equality", 87, 87);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = l_Lean_Name_mkStr3(x_8, x_2, x_3);
x_10 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(x_4, x_7, x_9, x_1);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_mk_string_unchecked("maxHeartbeats", 13, 13);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(200000u);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = lean_mk_string_unchecked("maximum amount of heartbeats per command. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit", 126, 126);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_8, x_2);
x_10 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_40__spec__0(x_3, x_7, x_9, x_1);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("async", 5, 5);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("perform elaboration using multiple threads where possible\n\nThis option defaults to `false` but (when not explicitly set) is overridden to `true` in the Lean language server and cmdline. Metaprogramming users driving elaboration directly via e.g. `Lean.Elab.Command.elabCommandTopLevel` can opt into asynchronous elaboration by setting this option but then are responsible for processing messages and other data not only in the resulting command state but also from async tasks in `Lean.Command.Context.snap\?` and `Lean.Command.State.snapshotTasks`.", 548, 548);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = l_Lean_Name_mkStr3(x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_8, x_10, x_1);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("inServer", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("true if elaboration is being run inside the Lean language server\n\nThis option is set by the file worker and should not be modified otherwise.", 141, 141);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = l_Lean_Name_mkStr3(x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_8, x_10, x_1);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("internal", 8, 8);
x_3 = lean_mk_string_unchecked("cmdlineSnapshots", 16, 16);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("reduce information stored in snapshots to the minimum necessary for the cmdline driver: diagnostics per command and final full snapshot", 135, 135);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = l_Lean_Name_mkStr3(x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_8, x_10, x_1);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_useDiagnosticMsg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_diagnostics;
x_5 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_mk_string_unchecked("\n\nAdditional diagnostic information may be available using the `set_option ", 75, 75);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_9, x_11, x_7);
x_13 = lean_string_append(x_8, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked(" true` command.", 15, 15);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_mk_string_unchecked("", 0, 0);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
}
}
static lean_object* _init_l_Lean_useDiagnosticMsg() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__2___boxed), 2, 0);
x_3 = l_Lean_MessageData_lazy(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_useDiagnosticMsg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_useDiagnosticMsg___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_useDiagnosticMsg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_useDiagnosticMsg___lam__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("Kernel", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("Core", 4, 4);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_mk_string_unchecked("initFn", 6, 6);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("_@", 2, 2);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = l_Lean_Name_str___override(x_13, x_6);
x_15 = lean_mk_string_unchecked("CoreM", 5, 5);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("_hyg", 4, 4);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_unsigned_to_nat(263u);
x_20 = l_Lean_Name_num___override(x_18, x_19);
x_21 = lean_unbox(x_4);
x_22 = l_Lean_registerTraceClass(x_3, x_21, x_20, x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_maxHeartbeats;
x_3 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_1, x_2);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMaxHeartbeats___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_instInhabitedCache() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_apply_3(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_4(x_4, x_9, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Core_instMonadCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_3 = l_instMonadEIO(lean_box(0));
x_4 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instMonadCoreM___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instInhabitedCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_ctor_get(x_4, 4);
x_12 = lean_ctor_get(x_4, 6);
x_13 = lean_ctor_get(x_4, 7);
x_14 = lean_ctor_get(x_4, 8);
x_15 = lean_ctor_get(x_4, 9);
x_16 = lean_ctor_get(x_4, 10);
x_17 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_18 = lean_ctor_get(x_4, 11);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_20 = lean_ctor_get(x_4, 12);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_10);
lean_ctor_set(x_21, 4, x_11);
lean_ctor_set(x_21, 5, x_2);
lean_ctor_set(x_21, 6, x_12);
lean_ctor_set(x_21, 7, x_13);
lean_ctor_set(x_21, 8, x_14);
lean_ctor_set(x_21, 9, x_15);
lean_ctor_set(x_21, 10, x_16);
lean_ctor_set(x_21, 11, x_18);
lean_ctor_set(x_21, 12, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*13, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*13 + 1, x_19);
x_22 = lean_apply_3(x_3, x_21, x_5, x_6);
return x_22;
}
}
static lean_object* _init_l_Lean_Core_instMonadRefCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRefCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRefCoreM___lam__1___boxed), 6, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRefCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRefCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_instMonadRefCoreM___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
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
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_15);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_15);
x_16 = lean_ctor_get(x_7, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 7);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_5);
lean_ctor_set(x_19, 5, x_16);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set(x_19, 7, x_18);
x_20 = lean_st_ref_set(x_3, x_19, x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_apply_1(x_1, x_29);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 3);
lean_inc(x_33);
x_34 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_ctor_get(x_27, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_27, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_27, 7);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_33);
lean_ctor_set(x_40, 4, x_36);
lean_ctor_set(x_40, 5, x_37);
lean_ctor_set(x_40, 6, x_38);
lean_ctor_set(x_40, 7, x_39);
x_41 = lean_st_ref_set(x_3, x_40, x_28);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadEnvCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadEnvCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadEnvCoreM___lam__1___boxed), 4, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadEnvCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadEnvCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadEnvCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instMonadOptionsCoreM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadOptionsCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadWithOptionsCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_73; uint8_t x_74; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = l_Lean_diagnostics;
x_14 = lean_apply_1(x_4, x_12);
x_15 = l_Lean_Option_get___redArg(x_1, x_14, x_13);
x_73 = lean_ctor_get(x_10, 0);
lean_inc(x_73);
lean_dec(x_10);
x_74 = l_Lean_Kernel_isDiagnosticsEnabled(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = lean_unbox(x_15);
if (x_75 == 0)
{
x_16 = x_6;
x_17 = x_7;
x_18 = x_11;
goto block_36;
}
else
{
goto block_72;
}
}
else
{
uint8_t x_76; 
x_76 = lean_unbox(x_15);
if (x_76 == 0)
{
goto block_72;
}
else
{
x_16 = x_6;
x_17 = x_7;
x_18 = x_11;
goto block_36;
}
}
block_36:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 3);
lean_inc(x_21);
x_22 = l_Lean_maxRecDepth;
x_23 = l_Lean_Option_get___redArg(x_2, x_14, x_22);
x_24 = lean_ctor_get(x_16, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 6);
lean_inc(x_25);
x_26 = lean_ctor_get(x_16, 7);
lean_inc(x_26);
x_27 = lean_ctor_get(x_16, 8);
lean_inc(x_27);
x_28 = lean_ctor_get(x_16, 9);
lean_inc(x_28);
x_29 = lean_ctor_get(x_16, 10);
lean_inc(x_29);
x_30 = lean_ctor_get(x_16, 11);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_16, sizeof(void*)*13 + 1);
x_32 = lean_ctor_get(x_16, 12);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_14);
lean_ctor_set(x_33, 3, x_21);
lean_ctor_set(x_33, 4, x_23);
lean_ctor_set(x_33, 5, x_24);
lean_ctor_set(x_33, 6, x_25);
lean_ctor_set(x_33, 7, x_26);
lean_ctor_set(x_33, 8, x_27);
lean_ctor_set(x_33, 9, x_28);
lean_ctor_set(x_33, 10, x_29);
lean_ctor_set(x_33, 11, x_30);
lean_ctor_set(x_33, 12, x_32);
x_34 = lean_unbox(x_15);
lean_dec(x_15);
lean_ctor_set_uint8(x_33, sizeof(void*)*13, x_34);
lean_ctor_set_uint8(x_33, sizeof(void*)*13 + 1, x_31);
x_35 = lean_apply_3(x_5, x_33, x_17, x_18);
return x_35;
}
block_72:
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_st_ref_take(x_7, x_11);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_15);
x_43 = l_Lean_Kernel_enableDiag(x_41, x_42);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 3);
lean_inc(x_46);
x_47 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_inc(x_48);
lean_ctor_set(x_37, 1, x_48);
lean_ctor_set(x_37, 0, x_48);
x_49 = lean_ctor_get(x_39, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 7);
lean_inc(x_51);
lean_dec(x_39);
x_52 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_45);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_37);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set(x_52, 6, x_50);
lean_ctor_set(x_52, 7, x_51);
x_53 = lean_st_ref_set(x_7, x_52, x_40);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_16 = x_6;
x_17 = x_7;
x_18 = x_54;
goto block_36;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_37);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_15);
x_59 = l_Lean_Kernel_enableDiag(x_57, x_58);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 3);
lean_inc(x_62);
x_63 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_inc(x_64);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_ctor_get(x_55, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 6);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 7);
lean_inc(x_68);
lean_dec(x_55);
x_69 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_60);
lean_ctor_set(x_69, 2, x_61);
lean_ctor_set(x_69, 3, x_62);
lean_ctor_set(x_69, 4, x_65);
lean_ctor_set(x_69, 5, x_66);
lean_ctor_set(x_69, 6, x_67);
lean_ctor_set(x_69, 7, x_68);
x_70 = lean_st_ref_set(x_7, x_69, x_56);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_16 = x_6;
x_17 = x_7;
x_18 = x_71;
goto block_36;
}
}
}
}
static lean_object* _init_l_Lean_Core_instMonadWithOptionsCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_KVMap_instValueBool;
x_2 = l_Lean_KVMap_instValueNat;
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadWithOptionsCoreM___lam__0), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_72; uint8_t x_73; 
x_5 = l_Lean_inheritedTraceOptions;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_KVMap_instValueBool;
x_10 = l_Lean_KVMap_instValueNat;
x_11 = lean_st_ref_get(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 3);
x_17 = lean_ctor_get(x_2, 5);
x_18 = lean_ctor_get(x_2, 6);
x_19 = lean_ctor_get(x_2, 7);
x_20 = lean_ctor_get(x_2, 8);
x_21 = lean_ctor_get(x_2, 9);
x_22 = lean_ctor_get(x_2, 10);
x_23 = lean_ctor_get(x_2, 11);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_diagnostics;
x_27 = l_Lean_Option_get___redArg(x_9, x_25, x_26);
x_72 = lean_ctor_get(x_12, 0);
lean_inc(x_72);
lean_dec(x_12);
x_73 = l_Lean_Kernel_isDiagnosticsEnabled(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = lean_unbox(x_27);
if (x_74 == 0)
{
x_28 = x_3;
x_29 = x_13;
goto block_35;
}
else
{
goto block_71;
}
}
else
{
uint8_t x_75; 
x_75 = lean_unbox(x_27);
if (x_75 == 0)
{
goto block_71;
}
else
{
x_28 = x_3;
x_29 = x_13;
goto block_35;
}
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = l_Lean_maxRecDepth;
x_31 = l_Lean_Option_get___redArg(x_10, x_25, x_30);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_25);
lean_inc(x_15);
lean_inc(x_14);
x_32 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_15);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_16);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_17);
lean_ctor_set(x_32, 6, x_18);
lean_ctor_set(x_32, 7, x_19);
lean_ctor_set(x_32, 8, x_20);
lean_ctor_set(x_32, 9, x_21);
lean_ctor_set(x_32, 10, x_22);
lean_ctor_set(x_32, 11, x_23);
lean_ctor_set(x_32, 12, x_7);
x_33 = lean_unbox(x_27);
lean_dec(x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*13, x_33);
lean_ctor_set_uint8(x_32, sizeof(void*)*13 + 1, x_24);
x_34 = lean_apply_3(x_1, x_32, x_28, x_29);
return x_34;
}
block_71:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_st_ref_take(x_3, x_13);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_27);
x_42 = l_Lean_Kernel_enableDiag(x_40, x_41);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_38, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 3);
lean_inc(x_45);
x_46 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_inc(x_47);
lean_ctor_set(x_36, 1, x_47);
lean_ctor_set(x_36, 0, x_47);
x_48 = lean_ctor_get(x_38, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_38, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 7);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_36);
lean_ctor_set(x_51, 5, x_48);
lean_ctor_set(x_51, 6, x_49);
lean_ctor_set(x_51, 7, x_50);
x_52 = lean_st_ref_set(x_3, x_51, x_39);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_28 = x_3;
x_29 = x_53;
goto block_35;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_54 = lean_ctor_get(x_36, 0);
x_55 = lean_ctor_get(x_36, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_36);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_27);
x_58 = l_Lean_Kernel_enableDiag(x_56, x_57);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 3);
lean_inc(x_61);
x_62 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_ctor_get(x_54, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_54, 7);
lean_inc(x_67);
lean_dec(x_54);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_3, x_68, x_55);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_28 = x_3;
x_29 = x_70;
goto block_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_89; uint8_t x_90; 
x_6 = l_Lean_inheritedTraceOptions;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_KVMap_instValueBool;
x_11 = l_Lean_KVMap_instValueNat;
x_12 = lean_st_ref_get(x_4, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get(x_3, 4);
x_19 = lean_ctor_get(x_3, 5);
x_20 = lean_ctor_get(x_3, 6);
x_21 = lean_ctor_get(x_3, 7);
x_22 = lean_ctor_get(x_3, 8);
x_23 = lean_ctor_get(x_3, 9);
x_24 = lean_ctor_get(x_3, 10);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*13);
x_26 = lean_ctor_get(x_3, 11);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_28);
lean_inc(x_16);
lean_inc(x_15);
x_29 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_18);
lean_ctor_set(x_29, 5, x_19);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_26);
lean_ctor_set(x_29, 12, x_8);
lean_ctor_set_uint8(x_29, sizeof(void*)*13, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*13 + 1, x_27);
x_30 = l_Lean_diagnostics;
x_31 = l_Lean_Option_get___redArg(x_10, x_28, x_30);
x_89 = lean_ctor_get(x_13, 0);
lean_inc(x_89);
lean_dec(x_13);
x_90 = l_Lean_Kernel_isDiagnosticsEnabled(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = lean_unbox(x_31);
if (x_91 == 0)
{
x_32 = x_29;
x_33 = x_4;
x_34 = x_14;
goto block_52;
}
else
{
goto block_88;
}
}
else
{
uint8_t x_92; 
x_92 = lean_unbox(x_31);
if (x_92 == 0)
{
goto block_88;
}
else
{
x_32 = x_29;
x_33 = x_4;
x_34 = x_14;
goto block_52;
}
}
block_52:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
x_38 = l_Lean_maxRecDepth;
x_39 = l_Lean_Option_get___redArg(x_11, x_28, x_38);
x_40 = lean_ctor_get(x_32, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_32, 6);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 7);
lean_inc(x_42);
x_43 = lean_ctor_get(x_32, 8);
lean_inc(x_43);
x_44 = lean_ctor_get(x_32, 9);
lean_inc(x_44);
x_45 = lean_ctor_get(x_32, 10);
lean_inc(x_45);
x_46 = lean_ctor_get(x_32, 11);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_32, sizeof(void*)*13 + 1);
x_48 = lean_ctor_get(x_32, 12);
lean_inc(x_48);
lean_dec(x_32);
lean_inc(x_28);
x_49 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_49, 2, x_28);
lean_ctor_set(x_49, 3, x_37);
lean_ctor_set(x_49, 4, x_39);
lean_ctor_set(x_49, 5, x_40);
lean_ctor_set(x_49, 6, x_41);
lean_ctor_set(x_49, 7, x_42);
lean_ctor_set(x_49, 8, x_43);
lean_ctor_set(x_49, 9, x_44);
lean_ctor_set(x_49, 10, x_45);
lean_ctor_set(x_49, 11, x_46);
lean_ctor_set(x_49, 12, x_48);
x_50 = lean_unbox(x_31);
lean_dec(x_31);
lean_ctor_set_uint8(x_49, sizeof(void*)*13, x_50);
lean_ctor_set_uint8(x_49, sizeof(void*)*13 + 1, x_47);
x_51 = lean_apply_3(x_2, x_49, x_33, x_34);
return x_51;
}
block_88:
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_st_ref_take(x_4, x_14);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_31);
x_59 = l_Lean_Kernel_enableDiag(x_57, x_58);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 3);
lean_inc(x_62);
x_63 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_inc(x_64);
lean_ctor_set(x_53, 1, x_64);
lean_ctor_set(x_53, 0, x_64);
x_65 = lean_ctor_get(x_55, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 7);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_61);
lean_ctor_set(x_68, 3, x_62);
lean_ctor_set(x_68, 4, x_53);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_4, x_68, x_56);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_32 = x_29;
x_33 = x_4;
x_34 = x_70;
goto block_52;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_71 = lean_ctor_get(x_53, 0);
x_72 = lean_ctor_get(x_53, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_53);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_31);
x_75 = l_Lean_Kernel_enableDiag(x_73, x_74);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 3);
lean_inc(x_78);
x_79 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_inc(x_80);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_ctor_get(x_71, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 6);
lean_inc(x_83);
x_84 = lean_ctor_get(x_71, 7);
lean_inc(x_84);
lean_dec(x_71);
x_85 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_76);
lean_ctor_set(x_85, 2, x_77);
lean_ctor_set(x_85, 3, x_78);
lean_ctor_set(x_85, 4, x_81);
lean_ctor_set(x_85, 5, x_82);
lean_ctor_set(x_85, 6, x_83);
lean_ctor_set(x_85, 7, x_84);
x_86 = lean_st_ref_set(x_4, x_85, x_72);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_32 = x_29;
x_33 = x_4;
x_34 = x_87;
goto block_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withConsistentCtx(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instAddMessageContextCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_3 = l_instMonadEIO(lean_box(0));
x_4 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = l_Lean_Core_instMonadEnvCoreM;
x_22 = lean_alloc_closure((void*)(l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed), 3, 0);
x_23 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial), 5, 4);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 2);
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
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 7);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
lean_ctor_set(x_15, 6, x_13);
lean_ctor_set(x_15, 7, x_14);
x_16 = lean_st_ref_set(x_3, x_15, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadNameGeneratorCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed), 4, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadNameGeneratorCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadNameGeneratorCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadNameGeneratorCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 2);
x_10 = lean_ctor_get(x_4, 4);
x_11 = lean_ctor_get(x_4, 5);
x_12 = lean_ctor_get(x_4, 6);
x_13 = lean_ctor_get(x_4, 7);
x_14 = lean_ctor_get(x_4, 8);
x_15 = lean_ctor_get(x_4, 9);
x_16 = lean_ctor_get(x_4, 10);
x_17 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_18 = lean_ctor_get(x_4, 11);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_20 = lean_ctor_get(x_4, 12);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_2);
lean_ctor_set(x_21, 4, x_10);
lean_ctor_set(x_21, 5, x_11);
lean_ctor_set(x_21, 6, x_12);
lean_ctor_set(x_21, 7, x_13);
lean_ctor_set(x_21, 8, x_14);
lean_ctor_set(x_21, 9, x_15);
lean_ctor_set(x_21, 10, x_16);
lean_ctor_set(x_21, 11, x_18);
lean_ctor_set(x_21, 12, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*13, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*13 + 1, x_19);
x_22 = lean_apply_3(x_3, x_21, x_5, x_6);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instMonadRecDepthCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lam__0___boxed), 6, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed), 3, 0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_instMonadRecDepthCoreM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadRecDepthCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadRecDepthCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 7);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instMonadResolveNameCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadResolveNameCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadResolveNameCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_8, x_10);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 7);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_14);
lean_ctor_set(x_18, 5, x_15);
lean_ctor_set(x_18, 6, x_16);
lean_ctor_set(x_18, 7, x_17);
x_19 = lean_st_ref_set(x_3, x_18, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = lean_ctor_get(x_2, 4);
x_26 = lean_ctor_get(x_2, 5);
x_27 = lean_ctor_get(x_2, 6);
x_28 = lean_ctor_get(x_2, 7);
x_29 = lean_ctor_get(x_2, 8);
x_30 = lean_ctor_get(x_2, 9);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_32 = lean_ctor_get(x_2, 11);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_34 = lean_ctor_get(x_2, 12);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_35 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set(x_35, 4, x_25);
lean_ctor_set(x_35, 5, x_26);
lean_ctor_set(x_35, 6, x_27);
lean_ctor_set(x_35, 7, x_28);
lean_ctor_set(x_35, 8, x_29);
lean_ctor_set(x_35, 9, x_30);
lean_ctor_set(x_35, 10, x_8);
lean_ctor_set(x_35, 11, x_32);
lean_ctor_set(x_35, 12, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*13, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*13 + 1, x_33);
x_36 = lean_apply_3(x_1, x_35, x_3, x_20);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withFreshMacroScope___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_withFreshMacroScope___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withFreshMacroScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withFreshMacroScope(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 10);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Environment_mainModule(x_7);
lean_dec(x_7);
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
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Environment_mainModule(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadQuotationCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed), 3, 0);
x_3 = l_Lean_Core_instMonadRefCoreM;
x_4 = lean_alloc_closure((void*)(l_Lean_Core_withFreshMacroScope___boxed), 5, 0);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadQuotationCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadQuotationCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 6);
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
x_10 = lean_ctor_get(x_8, 6);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 6);
lean_inc(x_14);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_ctor_get(x_6, 7);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_11);
lean_ctor_set(x_17, 4, x_12);
lean_ctor_set(x_17, 5, x_13);
lean_ctor_set(x_17, 6, x_15);
lean_ctor_set(x_17, 7, x_16);
x_18 = lean_st_ref_set(x_3, x_17, x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Core_instMonadInfoTreeCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed), 4, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadInfoTreeCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadInfoTreeCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadInfoTreeCoreM___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 4);
x_9 = lean_apply_1(x_1, x_8);
lean_ctor_set(x_5, 4, x_9);
x_10 = lean_st_ref_set(x_2, x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = lean_ctor_get(x_5, 6);
x_24 = lean_ctor_get(x_5, 7);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_25 = lean_apply_1(x_1, x_21);
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_22);
lean_ctor_set(x_26, 6, x_23);
lean_ctor_set(x_26, 7, x_24);
x_27 = lean_st_ref_set(x_2, x_26, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 4);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 4, x_10);
x_11 = lean_st_ref_set(x_3, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_26 = lean_apply_1(x_1, x_22);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
x_28 = lean_st_ref_set(x_3, x_27, x_7);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyCache___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 4);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_6, 0, x_12);
x_13 = lean_st_ref_set(x_2, x_5, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_apply_1(x_1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_5, 4, x_23);
x_24 = lean_st_ref_set(x_2, x_5, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 5);
x_34 = lean_ctor_get(x_5, 6);
x_35 = lean_ctor_get(x_5, 7);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_38 = x_6;
} else {
 lean_dec_ref(x_6);
 x_38 = lean_box(0);
}
x_39 = lean_apply_1(x_1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
x_42 = lean_st_ref_set(x_2, x_41, x_7);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 4);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_7, 0, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_apply_1(x_1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_6, 4, x_24);
x_25 = lean_st_ref_set(x_3, x_6, x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 5);
x_35 = lean_ctor_get(x_6, 6);
x_36 = lean_ctor_get(x_6, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_39 = x_7;
} else {
 lean_dec_ref(x_7);
 x_39 = lean_box(0);
}
x_40 = lean_apply_1(x_1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_34);
lean_ctor_set(x_42, 6, x_35);
lean_ctor_set(x_42, 7, x_36);
x_43 = lean_st_ref_set(x_3, x_42, x_8);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyInstLevelTypeCache___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelTypeCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyInstLevelTypeCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 4);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_6, 1, x_12);
x_13 = lean_st_ref_set(x_2, x_5, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_apply_1(x_1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_5, 4, x_23);
x_24 = lean_st_ref_set(x_2, x_5, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 5);
x_34 = lean_ctor_get(x_5, 6);
x_35 = lean_ctor_get(x_5, 7);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_38 = x_6;
} else {
 lean_dec_ref(x_6);
 x_38 = lean_box(0);
}
x_39 = lean_apply_1(x_1, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
x_42 = lean_st_ref_set(x_2, x_41, x_7);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 4);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_7, 1, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_6, 4, x_24);
x_25 = lean_st_ref_set(x_3, x_6, x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 5);
x_35 = lean_ctor_get(x_6, 6);
x_36 = lean_ctor_get(x_6, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_39 = x_7;
} else {
 lean_dec_ref(x_7);
 x_39 = lean_box(0);
}
x_40 = lean_apply_1(x_1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_34);
lean_ctor_set(x_42, 6, x_35);
lean_ctor_set(x_42, 7, x_36);
x_43 = lean_st_ref_set(x_3, x_42, x_8);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_modifyInstLevelValueCache___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_modifyInstLevelValueCache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_modifyInstLevelValueCache(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_level_eq(x_9, x_11);
if (x_13 == 0)
{
return x_13;
}
else
{
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_80 = lean_ctor_get(x_7, 4);
lean_inc(x_80);
lean_dec(x_7);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_box(0), x_81, x_82);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_free_object(x_5);
x_9 = x_3;
goto block_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_2, x_85);
lean_dec(x_85);
if (x_87 == 0)
{
lean_dec(x_86);
lean_free_object(x_5);
x_9 = x_3;
goto block_79;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_86);
return x_5;
}
}
block_79:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 4);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_20);
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_2);
x_22 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_19, x_21, x_10);
lean_ctor_set(x_12, 0, x_22);
x_23 = lean_st_ref_set(x_9, x_11, x_14);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
lean_inc(x_30);
lean_ctor_set(x_10, 1, x_30);
lean_ctor_set(x_10, 0, x_2);
x_32 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_28, x_31, x_10);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_11, 4, x_33);
x_34 = lean_st_ref_set(x_9, x_11, x_14);
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
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
x_40 = lean_ctor_get(x_11, 2);
x_41 = lean_ctor_get(x_11, 3);
x_42 = lean_ctor_get(x_11, 5);
x_43 = lean_ctor_get(x_11, 6);
x_44 = lean_ctor_get(x_11, 7);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_45 = lean_ctor_get(x_12, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_47 = x_12;
} else {
 lean_dec_ref(x_12);
 x_47 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
lean_inc(x_48);
lean_ctor_set(x_10, 1, x_48);
lean_ctor_set(x_10, 0, x_2);
x_50 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_45, x_49, x_10);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_47;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
x_52 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_39);
lean_ctor_set(x_52, 2, x_40);
lean_ctor_set(x_52, 3, x_41);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_42);
lean_ctor_set(x_52, 6, x_43);
lean_ctor_set(x_52, 7, x_44);
x_53 = lean_st_ref_set(x_9, x_52, x_14);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_57 = lean_ctor_get(x_10, 1);
lean_inc(x_57);
lean_dec(x_10);
x_58 = lean_ctor_get(x_11, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_11, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_11, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_11, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_11, 7);
lean_inc(x_64);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 lean_ctor_release(x_11, 7);
 x_65 = x_11;
} else {
 lean_dec_ref(x_11);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_12, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_68 = x_12;
} else {
 lean_dec_ref(x_12);
 x_68 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_69 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
lean_inc(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_66, x_70, x_71);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(0, 8, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_58);
lean_ctor_set(x_74, 1, x_59);
lean_ctor_set(x_74, 2, x_60);
lean_ctor_set(x_74, 3, x_61);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_74, 5, x_62);
lean_ctor_set(x_74, 6, x_63);
lean_ctor_set(x_74, 7, x_64);
x_75 = lean_st_ref_set(x_9, x_74, x_57);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_88 = lean_ctor_get(x_5, 0);
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_5);
x_118 = lean_ctor_get(x_88, 4);
lean_inc(x_118);
lean_dec(x_88);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
x_121 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_box(0), x_119, x_120);
lean_dec(x_120);
if (lean_obj_tag(x_121) == 0)
{
x_90 = x_3;
goto block_117;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_2, x_123);
lean_dec(x_123);
if (x_125 == 0)
{
lean_dec(x_124);
x_90 = x_3;
goto block_117;
}
else
{
lean_object* x_126; 
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_89);
return x_126;
}
}
block_117:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_91 = lean_st_ref_take(x_90, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_92, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_92, 6);
lean_inc(x_101);
x_102 = lean_ctor_get(x_92, 7);
lean_inc(x_102);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 lean_ctor_release(x_92, 5);
 lean_ctor_release(x_92, 6);
 lean_ctor_release(x_92, 7);
 x_103 = x_92;
} else {
 lean_dec_ref(x_92);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_93, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_93, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_106 = x_93;
} else {
 lean_dec_ref(x_93);
 x_106 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_107 = l_Lean_ConstantVal_instantiateTypeLevelParams(x_1, x_2);
x_108 = lean_ctor_get(x_1, 0);
lean_inc(x_108);
lean_dec(x_1);
lean_inc(x_107);
if (lean_is_scalar(x_95)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_95;
}
lean_ctor_set(x_109, 0, x_2);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_104, x_108, x_109);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_106;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
if (lean_is_scalar(x_103)) {
 x_112 = lean_alloc_ctor(0, 8, 0);
} else {
 x_112 = x_103;
}
lean_ctor_set(x_112, 0, x_96);
lean_ctor_set(x_112, 1, x_97);
lean_ctor_set(x_112, 2, x_98);
lean_ctor_set(x_112, 3, x_99);
lean_ctor_set(x_112, 4, x_111);
lean_ctor_set(x_112, 5, x_100);
lean_ctor_set(x_112, 6, x_101);
lean_ctor_set(x_112, 7, x_102);
x_113 = lean_st_ref_set(x_90, x_112, x_94);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateTypeLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateTypeLevelParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_11);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
lean_inc(x_11);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
lean_inc(x_11);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_10);
lean_ctor_set(x_18, 3, x_12);
lean_ctor_set(x_18, 4, x_13);
lean_ctor_set(x_18, 5, x_14);
lean_ctor_set(x_18, 6, x_15);
lean_ctor_set(x_18, 7, x_16);
lean_ctor_set(x_18, 8, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_11);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_unsigned_to_nat(5u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_to_nat(x_22);
x_24 = lean_nat_pow(x_20, x_23);
lean_dec(x_23);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = lean_usize_to_nat(x_25);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_10);
lean_ctor_set(x_29, 3, x_10);
lean_ctor_set_usize(x_29, 4, x_22);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_inc(x_9);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_9);
x_33 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_1);
lean_ctor_set(x_5, 0, x_33);
return x_5;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_39);
lean_inc(x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_39);
lean_inc(x_39);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_39);
lean_inc(x_39);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_39);
lean_inc(x_39);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_39);
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_38);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_43);
lean_ctor_set(x_46, 7, x_44);
lean_ctor_set(x_46, 8, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_39);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_unsigned_to_nat(5u);
x_50 = lean_usize_of_nat(x_49);
x_51 = lean_usize_to_nat(x_50);
x_52 = lean_nat_pow(x_48, x_51);
lean_dec(x_51);
x_53 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_54 = lean_usize_to_nat(x_53);
x_55 = lean_mk_empty_array_with_capacity(x_54);
lean_dec(x_54);
lean_inc(x_55);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_38);
lean_ctor_set(x_57, 3, x_38);
lean_ctor_set_usize(x_57, 4, x_50);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_58);
lean_inc(x_37);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_36);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_37);
x_61 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_35);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_tag(x_5, 1);
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
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_98 = lean_ctor_get(x_8, 4);
lean_inc(x_98);
lean_dec(x_8);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_ConstantInfo_name(x_1);
x_101 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_box(0), x_99, x_100);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_free_object(x_6);
x_10 = x_3;
x_11 = x_4;
goto block_97;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_2, x_103);
lean_dec(x_103);
if (x_105 == 0)
{
lean_dec(x_104);
lean_free_object(x_6);
x_10 = x_3;
x_11 = x_4;
goto block_97;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_6, 0, x_104);
return x_6;
}
}
block_97:
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_ConstantInfo_hasValue(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_2);
x_15 = lean_mk_string_unchecked("Not a definition or theorem: ", 29, 29);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_ConstantInfo_name(x_1);
x_18 = l_Lean_MessageData_ofName(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_22, x_10, x_11, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_take(x_11, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 4);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 1);
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_29, 4);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_2);
x_38 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_39 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_38);
lean_ctor_set(x_28, 1, x_38);
lean_ctor_set(x_28, 0, x_2);
x_40 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_37, x_39, x_28);
lean_ctor_set(x_30, 1, x_40);
x_41 = lean_st_ref_set(x_11, x_29, x_32);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_38);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
lean_inc(x_2);
x_48 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_49 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_48);
lean_ctor_set(x_28, 1, x_48);
lean_ctor_set(x_28, 0, x_2);
x_50 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_47, x_49, x_28);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_29, 4, x_51);
x_52 = lean_st_ref_set(x_11, x_29, x_32);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_56 = lean_ctor_get(x_29, 0);
x_57 = lean_ctor_get(x_29, 1);
x_58 = lean_ctor_get(x_29, 2);
x_59 = lean_ctor_get(x_29, 3);
x_60 = lean_ctor_get(x_29, 5);
x_61 = lean_ctor_get(x_29, 6);
x_62 = lean_ctor_get(x_29, 7);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_29);
x_63 = lean_ctor_get(x_30, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_65 = x_30;
} else {
 lean_dec_ref(x_30);
 x_65 = lean_box(0);
}
lean_inc(x_2);
x_66 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_67 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_66);
lean_ctor_set(x_28, 1, x_66);
lean_ctor_set(x_28, 0, x_2);
x_68 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_64, x_67, x_28);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_70, 0, x_56);
lean_ctor_set(x_70, 1, x_57);
lean_ctor_set(x_70, 2, x_58);
lean_ctor_set(x_70, 3, x_59);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_60);
lean_ctor_set(x_70, 6, x_61);
lean_ctor_set(x_70, 7, x_62);
x_71 = lean_st_ref_set(x_11, x_70, x_32);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_75 = lean_ctor_get(x_28, 1);
lean_inc(x_75);
lean_dec(x_28);
x_76 = lean_ctor_get(x_29, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_29, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_29, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_29, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_29, 5);
lean_inc(x_80);
x_81 = lean_ctor_get(x_29, 6);
lean_inc(x_81);
x_82 = lean_ctor_get(x_29, 7);
lean_inc(x_82);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 x_83 = x_29;
} else {
 lean_dec_ref(x_29);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_30, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_30, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_86 = x_30;
} else {
 lean_dec_ref(x_30);
 x_86 = lean_box(0);
}
lean_inc(x_2);
x_87 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_88 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_2);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_85, x_88, x_89);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_90);
if (lean_is_scalar(x_83)) {
 x_92 = lean_alloc_ctor(0, 8, 0);
} else {
 x_92 = x_83;
}
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_77);
lean_ctor_set(x_92, 2, x_78);
lean_ctor_set(x_92, 3, x_79);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set(x_92, 5, x_80);
lean_ctor_set(x_92, 6, x_81);
lean_ctor_set(x_92, 7, x_82);
x_93 = lean_st_ref_set(x_11, x_92, x_75);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_106 = lean_ctor_get(x_6, 0);
x_107 = lean_ctor_get(x_6, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_6);
x_153 = lean_ctor_get(x_106, 4);
lean_inc(x_153);
lean_dec(x_106);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_155 = l_Lean_ConstantInfo_name(x_1);
x_156 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1(lean_box(0), x_154, x_155);
lean_dec(x_155);
if (lean_obj_tag(x_156) == 0)
{
x_108 = x_3;
x_109 = x_4;
goto block_152;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec(x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_List_beq___at___Lean_Core_instantiateTypeLevelParams_spec__0(x_2, x_158);
lean_dec(x_158);
if (x_160 == 0)
{
lean_dec(x_159);
x_108 = x_3;
x_109 = x_4;
goto block_152;
}
else
{
lean_object* x_161; 
lean_dec(x_2);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_107);
return x_161;
}
}
block_152:
{
lean_object* x_110; uint8_t x_111; uint8_t x_112; 
x_110 = lean_box(0);
x_111 = lean_unbox(x_110);
x_112 = l_Lean_ConstantInfo_hasValue(x_1, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_2);
x_113 = lean_mk_string_unchecked("Not a definition or theorem: ", 29, 29);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = l_Lean_ConstantInfo_name(x_1);
x_116 = l_Lean_MessageData_ofName(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("", 0, 0);
x_119 = l_Lean_stringToMessageData(x_118);
lean_dec(x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_120, x_108, x_109, x_107);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_126 = lean_st_ref_take(x_109, x_107);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 5);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 6);
lean_inc(x_136);
x_137 = lean_ctor_get(x_127, 7);
lean_inc(x_137);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 lean_ctor_release(x_127, 6);
 lean_ctor_release(x_127, 7);
 x_138 = x_127;
} else {
 lean_dec_ref(x_127);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_128, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_128, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_141 = x_128;
} else {
 lean_dec_ref(x_128);
 x_141 = lean_box(0);
}
lean_inc(x_2);
x_142 = l_Lean_ConstantInfo_instantiateValueLevelParams_x21(x_1, x_2);
x_143 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_142);
if (lean_is_scalar(x_130)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_130;
}
lean_ctor_set(x_144, 0, x_2);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_140, x_143, x_144);
if (lean_is_scalar(x_141)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_141;
}
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_145);
if (lean_is_scalar(x_138)) {
 x_147 = lean_alloc_ctor(0, 8, 0);
} else {
 x_147 = x_138;
}
lean_ctor_set(x_147, 0, x_131);
lean_ctor_set(x_147, 1, x_132);
lean_ctor_set(x_147, 2, x_133);
lean_ctor_set(x_147, 3, x_134);
lean_ctor_set(x_147, 4, x_146);
lean_ctor_set(x_147, 5, x_135);
lean_ctor_set(x_147, 6, x_136);
lean_ctor_set(x_147, 7, x_137);
x_148 = lean_st_ref_set(x_109, x_147, x_129);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instantiateValueLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
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
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_io_error_to_string(x_10);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_ofFormat(x_13);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_ctor_get(x_2, 5);
x_19 = lean_io_error_to_string(x_16);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
lean_inc(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
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
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_io_error_to_string(x_12);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_ctor_get(x_3, 5);
x_21 = lean_io_error_to_string(x_18);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
lean_inc(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_liftIOCore___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_liftIOCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_liftIOCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Core_instMonadLiftIOCoreM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 3);
lean_inc(x_11);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 7);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_14);
lean_ctor_set(x_17, 6, x_15);
lean_ctor_set(x_17, 7, x_16);
x_18 = lean_st_ref_set(x_3, x_17, x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 12);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_instMonadTraceCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lam__0___boxed), 4, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadTraceCoreM___lam__2___boxed), 3, 0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadTraceCoreM___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadTraceCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadTraceCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_saveState___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_saveState___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_saveState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_saveState(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_io_get_num_heartbeats(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_4);
x_10 = lean_apply_3(x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_12);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_io_get_num_heartbeats(x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_nat_sub(x_18, x_8);
lean_dec(x_8);
lean_dec(x_18);
lean_ctor_set(x_13, 1, x_19);
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_nat_sub(x_20, x_8);
lean_dec(x_8);
lean_dec(x_20);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_6, 1, x_13);
lean_ctor_set(x_6, 0, x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_io_get_num_heartbeats(x_25);
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
x_30 = lean_nat_sub(x_27, x_8);
lean_dec(x_8);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_11);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_8);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
return x_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
lean_inc(x_4);
x_39 = lean_apply_3(x_2, x_3, x_4, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_get(x_4, x_41);
lean_dec(x_4);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_io_get_num_heartbeats(x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_nat_sub(x_47, x_37);
lean_dec(x_37);
lean_dec(x_47);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_51);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_37);
lean_dec(x_4);
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_56 = x_39;
} else {
 lean_dec_ref(x_39);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
lean_dec(x_1);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_st_ref_set(x_4, x_60, x_5);
lean_dec(x_4);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = l_IO_addHeartbeats(x_63, x_62);
lean_dec(x_63);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_58);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withRestoreOrSaveFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_withRestoreOrSaveFull___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 5);
x_14 = lean_ctor_get(x_7, 6);
x_15 = lean_ctor_get(x_5, 7);
lean_inc(x_15);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_8);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_11);
lean_ctor_set(x_16, 4, x_12);
lean_ctor_set(x_16, 5, x_13);
lean_ctor_set(x_16, 6, x_14);
lean_ctor_set(x_16, 7, x_15);
x_17 = lean_st_ref_set(x_2, x_16, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_SavedState_restore___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_SavedState_restore___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_SavedState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_SavedState_restore(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 7);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_14);
lean_ctor_set(x_17, 6, x_15);
lean_ctor_set(x_17, 7, x_16);
x_18 = lean_st_ref_set(x_2, x_17, x_6);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_2, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Environment_mainModule(x_23);
lean_dec(x_23);
x_25 = l_Lean_addMacroScope(x_24, x_1, x_7);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Environment_mainModule(x_28);
lean_dec(x_28);
x_30 = l_Lean_addMacroScope(x_29, x_1, x_7);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_mkFreshUserName___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_mkFreshUserName(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_90; uint8_t x_91; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_inheritedTraceOptions;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_KVMap_instValueBool;
x_13 = l_Lean_KVMap_instValueNat;
x_14 = lean_st_ref_get(x_6, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 5);
x_22 = lean_ctor_get(x_2, 6);
x_23 = lean_ctor_get(x_2, 7);
x_24 = lean_ctor_get(x_2, 8);
x_25 = lean_ctor_get(x_2, 9);
x_26 = lean_ctor_get(x_2, 10);
x_27 = lean_ctor_get(x_2, 11);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = l_Lean_diagnostics;
x_31 = l_Lean_Option_get___redArg(x_12, x_29, x_30);
x_90 = lean_ctor_get(x_15, 0);
lean_inc(x_90);
lean_dec(x_15);
x_91 = l_Lean_Kernel_isDiagnosticsEnabled(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = lean_unbox(x_31);
if (x_92 == 0)
{
lean_inc(x_6);
x_32 = x_6;
x_33 = x_16;
goto block_53;
}
else
{
goto block_89;
}
}
else
{
uint8_t x_93; 
x_93 = lean_unbox(x_31);
if (x_93 == 0)
{
goto block_89;
}
else
{
lean_inc(x_6);
x_32 = x_6;
x_33 = x_16;
goto block_53;
}
}
block_53:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = l_Lean_maxRecDepth;
x_35 = l_Lean_Option_get___redArg(x_13, x_29, x_34);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_29);
lean_inc(x_19);
lean_inc(x_18);
x_36 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_19);
lean_ctor_set(x_36, 2, x_29);
lean_ctor_set(x_36, 3, x_20);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_21);
lean_ctor_set(x_36, 6, x_22);
lean_ctor_set(x_36, 7, x_23);
lean_ctor_set(x_36, 8, x_24);
lean_ctor_set(x_36, 9, x_25);
lean_ctor_set(x_36, 10, x_26);
lean_ctor_set(x_36, 11, x_27);
lean_ctor_set(x_36, 12, x_10);
x_37 = lean_unbox(x_31);
lean_dec(x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*13, x_37);
lean_ctor_set_uint8(x_36, sizeof(void*)*13 + 1, x_28);
x_38 = lean_apply_3(x_1, x_36, x_32, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_6, x_40);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
if (lean_is_scalar(x_17)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_17;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
if (lean_is_scalar(x_17)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_17;
}
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_6);
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
block_89:
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_st_ref_take(x_6, x_16);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_31);
x_60 = l_Lean_Kernel_enableDiag(x_58, x_59);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 3);
lean_inc(x_63);
x_64 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_inc(x_65);
lean_ctor_set(x_54, 1, x_65);
lean_ctor_set(x_54, 0, x_65);
x_66 = lean_ctor_get(x_56, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_56, 6);
lean_inc(x_67);
x_68 = lean_ctor_get(x_56, 7);
lean_inc(x_68);
lean_dec(x_56);
x_69 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_54);
lean_ctor_set(x_69, 5, x_66);
lean_ctor_set(x_69, 6, x_67);
lean_ctor_set(x_69, 7, x_68);
x_70 = lean_st_ref_set(x_6, x_69, x_57);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_6);
x_32 = x_6;
x_33 = x_71;
goto block_53;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_72 = lean_ctor_get(x_54, 0);
x_73 = lean_ctor_get(x_54, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_54);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_31);
x_76 = l_Lean_Kernel_enableDiag(x_74, x_75);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 3);
lean_inc(x_79);
x_80 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_inc(x_81);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_ctor_get(x_72, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_72, 6);
lean_inc(x_84);
x_85 = lean_ctor_get(x_72, 7);
lean_inc(x_85);
lean_dec(x_72);
x_86 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_77);
lean_ctor_set(x_86, 2, x_78);
lean_ctor_set(x_86, 3, x_79);
lean_ctor_set(x_86, 4, x_82);
lean_ctor_set(x_86, 5, x_83);
lean_ctor_set(x_86, 6, x_84);
lean_ctor_set(x_86, 7, x_85);
x_87 = lean_st_ref_set(x_6, x_86, x_73);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
lean_inc(x_6);
x_32 = x_6;
x_33 = x_88;
goto block_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_107; uint8_t x_108; 
x_6 = lean_st_mk_ref(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_inheritedTraceOptions;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_KVMap_instValueBool;
x_14 = l_Lean_KVMap_instValueNat;
x_15 = lean_st_ref_get(x_7, x_12);
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
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 5);
x_24 = lean_ctor_get(x_3, 6);
x_25 = lean_ctor_get(x_3, 7);
x_26 = lean_ctor_get(x_3, 8);
x_27 = lean_ctor_get(x_3, 9);
x_28 = lean_ctor_get(x_3, 10);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*13);
x_30 = lean_ctor_get(x_3, 11);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
x_32 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_32);
lean_inc(x_20);
lean_inc(x_19);
x_33 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_21);
lean_ctor_set(x_33, 4, x_22);
lean_ctor_set(x_33, 5, x_23);
lean_ctor_set(x_33, 6, x_24);
lean_ctor_set(x_33, 7, x_25);
lean_ctor_set(x_33, 8, x_26);
lean_ctor_set(x_33, 9, x_27);
lean_ctor_set(x_33, 10, x_28);
lean_ctor_set(x_33, 11, x_30);
lean_ctor_set(x_33, 12, x_11);
lean_ctor_set_uint8(x_33, sizeof(void*)*13, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*13 + 1, x_31);
x_34 = l_Lean_diagnostics;
x_35 = l_Lean_Option_get___redArg(x_13, x_32, x_34);
x_107 = lean_ctor_get(x_16, 0);
lean_inc(x_107);
lean_dec(x_16);
x_108 = l_Lean_Kernel_isDiagnosticsEnabled(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = lean_unbox(x_35);
if (x_109 == 0)
{
lean_inc(x_7);
x_36 = x_33;
x_37 = x_7;
x_38 = x_17;
goto block_70;
}
else
{
goto block_106;
}
}
else
{
uint8_t x_110; 
x_110 = lean_unbox(x_35);
if (x_110 == 0)
{
goto block_106;
}
else
{
lean_inc(x_7);
x_36 = x_33;
x_37 = x_7;
x_38 = x_17;
goto block_70;
}
}
block_70:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 3);
lean_inc(x_41);
x_42 = l_Lean_maxRecDepth;
x_43 = l_Lean_Option_get___redArg(x_14, x_32, x_42);
x_44 = lean_ctor_get(x_36, 5);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 6);
lean_inc(x_45);
x_46 = lean_ctor_get(x_36, 7);
lean_inc(x_46);
x_47 = lean_ctor_get(x_36, 8);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 9);
lean_inc(x_48);
x_49 = lean_ctor_get(x_36, 10);
lean_inc(x_49);
x_50 = lean_ctor_get(x_36, 11);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_36, sizeof(void*)*13 + 1);
x_52 = lean_ctor_get(x_36, 12);
lean_inc(x_52);
lean_dec(x_36);
lean_inc(x_32);
x_53 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_53, 2, x_32);
lean_ctor_set(x_53, 3, x_41);
lean_ctor_set(x_53, 4, x_43);
lean_ctor_set(x_53, 5, x_44);
lean_ctor_set(x_53, 6, x_45);
lean_ctor_set(x_53, 7, x_46);
lean_ctor_set(x_53, 8, x_47);
lean_ctor_set(x_53, 9, x_48);
lean_ctor_set(x_53, 10, x_49);
lean_ctor_set(x_53, 11, x_50);
lean_ctor_set(x_53, 12, x_52);
x_54 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_53, sizeof(void*)*13, x_54);
lean_ctor_set_uint8(x_53, sizeof(void*)*13 + 1, x_51);
x_55 = lean_apply_3(x_2, x_53, x_37, x_38);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_st_ref_get(x_7, x_57);
lean_dec(x_7);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
if (lean_is_scalar(x_18)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_18;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
if (lean_is_scalar(x_18)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_18;
}
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_18);
lean_dec(x_7);
x_66 = !lean_is_exclusive(x_55);
if (x_66 == 0)
{
return x_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_55, 0);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_55);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
block_106:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_st_ref_take(x_7, x_17);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_35);
x_77 = l_Lean_Kernel_enableDiag(x_75, x_76);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 3);
lean_inc(x_80);
x_81 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
lean_inc(x_82);
lean_ctor_set(x_71, 1, x_82);
lean_ctor_set(x_71, 0, x_82);
x_83 = lean_ctor_get(x_73, 5);
lean_inc(x_83);
x_84 = lean_ctor_get(x_73, 6);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 7);
lean_inc(x_85);
lean_dec(x_73);
x_86 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_78);
lean_ctor_set(x_86, 2, x_79);
lean_ctor_set(x_86, 3, x_80);
lean_ctor_set(x_86, 4, x_71);
lean_ctor_set(x_86, 5, x_83);
lean_ctor_set(x_86, 6, x_84);
lean_ctor_set(x_86, 7, x_85);
x_87 = lean_st_ref_set(x_7, x_86, x_74);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
lean_inc(x_7);
x_36 = x_33;
x_37 = x_7;
x_38 = x_88;
goto block_70;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_89 = lean_ctor_get(x_71, 0);
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_71);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_35);
x_93 = l_Lean_Kernel_enableDiag(x_91, x_92);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 3);
lean_inc(x_96);
x_97 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
lean_inc(x_98);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_ctor_get(x_89, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_89, 6);
lean_inc(x_101);
x_102 = lean_ctor_get(x_89, 7);
lean_inc(x_102);
lean_dec(x_89);
x_103 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_94);
lean_ctor_set(x_103, 2, x_95);
lean_ctor_set(x_103, 3, x_96);
lean_ctor_set(x_103, 4, x_99);
lean_ctor_set(x_103, 5, x_100);
lean_ctor_set(x_103, 6, x_101);
lean_ctor_set(x_103, 7, x_102);
x_104 = lean_st_ref_set(x_7, x_103, x_90);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
lean_inc(x_7);
x_36 = x_33;
x_37 = x_7;
x_38 = x_105;
goto block_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_CoreM_run___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_CoreM_run(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_82; uint8_t x_83; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_inheritedTraceOptions;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_KVMap_instValueBool;
x_13 = l_Lean_KVMap_instValueNat;
x_14 = lean_st_ref_get(x_6, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 3);
x_20 = lean_ctor_get(x_2, 5);
x_21 = lean_ctor_get(x_2, 6);
x_22 = lean_ctor_get(x_2, 7);
x_23 = lean_ctor_get(x_2, 8);
x_24 = lean_ctor_get(x_2, 9);
x_25 = lean_ctor_get(x_2, 10);
x_26 = lean_ctor_get(x_2, 11);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_2, 2);
x_29 = l_Lean_diagnostics;
x_30 = l_Lean_Option_get___redArg(x_12, x_28, x_29);
x_82 = lean_ctor_get(x_15, 0);
lean_inc(x_82);
lean_dec(x_15);
x_83 = l_Lean_Kernel_isDiagnosticsEnabled(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = lean_unbox(x_30);
if (x_84 == 0)
{
lean_inc(x_6);
x_31 = x_6;
x_32 = x_16;
goto block_45;
}
else
{
goto block_81;
}
}
else
{
uint8_t x_85; 
x_85 = lean_unbox(x_30);
if (x_85 == 0)
{
goto block_81;
}
else
{
lean_inc(x_6);
x_31 = x_6;
x_32 = x_16;
goto block_45;
}
}
block_45:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = l_Lean_maxRecDepth;
x_34 = l_Lean_Option_get___redArg(x_13, x_28, x_33);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_28);
lean_inc(x_18);
lean_inc(x_17);
x_35 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_18);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_19);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_20);
lean_ctor_set(x_35, 6, x_21);
lean_ctor_set(x_35, 7, x_22);
lean_ctor_set(x_35, 8, x_23);
lean_ctor_set(x_35, 9, x_24);
lean_ctor_set(x_35, 10, x_25);
lean_ctor_set(x_35, 11, x_26);
lean_ctor_set(x_35, 12, x_10);
x_36 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*13, x_36);
lean_ctor_set_uint8(x_35, sizeof(void*)*13 + 1, x_27);
x_37 = lean_apply_3(x_1, x_35, x_31, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_st_ref_get(x_6, x_39);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_dec(x_6);
return x_37;
}
}
block_81:
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_st_ref_take(x_6, x_16);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_30);
x_52 = l_Lean_Kernel_enableDiag(x_50, x_51);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 3);
lean_inc(x_55);
x_56 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_inc(x_57);
lean_ctor_set(x_46, 1, x_57);
lean_ctor_set(x_46, 0, x_57);
x_58 = lean_ctor_get(x_48, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_48, 6);
lean_inc(x_59);
x_60 = lean_ctor_get(x_48, 7);
lean_inc(x_60);
lean_dec(x_48);
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_54);
lean_ctor_set(x_61, 3, x_55);
lean_ctor_set(x_61, 4, x_46);
lean_ctor_set(x_61, 5, x_58);
lean_ctor_set(x_61, 6, x_59);
lean_ctor_set(x_61, 7, x_60);
x_62 = lean_st_ref_set(x_6, x_61, x_49);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_6);
x_31 = x_6;
x_32 = x_63;
goto block_45;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_64 = lean_ctor_get(x_46, 0);
x_65 = lean_ctor_get(x_46, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_46);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_30);
x_68 = l_Lean_Kernel_enableDiag(x_66, x_67);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 3);
lean_inc(x_71);
x_72 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_inc(x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_ctor_get(x_64, 5);
lean_inc(x_75);
x_76 = lean_ctor_get(x_64, 6);
lean_inc(x_76);
x_77 = lean_ctor_get(x_64, 7);
lean_inc(x_77);
lean_dec(x_64);
x_78 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_69);
lean_ctor_set(x_78, 2, x_70);
lean_ctor_set(x_78, 3, x_71);
lean_ctor_set(x_78, 4, x_74);
lean_ctor_set(x_78, 5, x_75);
lean_ctor_set(x_78, 6, x_76);
lean_ctor_set(x_78, 7, x_77);
x_79 = lean_st_ref_set(x_6, x_78, x_65);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_inc(x_6);
x_31 = x_6;
x_32 = x_80;
goto block_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_99; uint8_t x_100; 
x_6 = lean_st_mk_ref(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_inheritedTraceOptions;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_KVMap_instValueBool;
x_14 = l_Lean_KVMap_instValueNat;
x_15 = lean_st_ref_get(x_7, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 3);
x_21 = lean_ctor_get(x_3, 4);
x_22 = lean_ctor_get(x_3, 5);
x_23 = lean_ctor_get(x_3, 6);
x_24 = lean_ctor_get(x_3, 7);
x_25 = lean_ctor_get(x_3, 8);
x_26 = lean_ctor_get(x_3, 9);
x_27 = lean_ctor_get(x_3, 10);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*13);
x_29 = lean_ctor_get(x_3, 11);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_31);
lean_inc(x_19);
lean_inc(x_18);
x_32 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_20);
lean_ctor_set(x_32, 4, x_21);
lean_ctor_set(x_32, 5, x_22);
lean_ctor_set(x_32, 6, x_23);
lean_ctor_set(x_32, 7, x_24);
lean_ctor_set(x_32, 8, x_25);
lean_ctor_set(x_32, 9, x_26);
lean_ctor_set(x_32, 10, x_27);
lean_ctor_set(x_32, 11, x_29);
lean_ctor_set(x_32, 12, x_11);
lean_ctor_set_uint8(x_32, sizeof(void*)*13, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*13 + 1, x_30);
x_33 = l_Lean_diagnostics;
x_34 = l_Lean_Option_get___redArg(x_13, x_31, x_33);
x_99 = lean_ctor_get(x_16, 0);
lean_inc(x_99);
lean_dec(x_16);
x_100 = l_Lean_Kernel_isDiagnosticsEnabled(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = lean_unbox(x_34);
if (x_101 == 0)
{
lean_inc(x_7);
x_35 = x_32;
x_36 = x_7;
x_37 = x_17;
goto block_62;
}
else
{
goto block_98;
}
}
else
{
uint8_t x_102; 
x_102 = lean_unbox(x_34);
if (x_102 == 0)
{
goto block_98;
}
else
{
lean_inc(x_7);
x_35 = x_32;
x_36 = x_7;
x_37 = x_17;
goto block_62;
}
}
block_62:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 3);
lean_inc(x_40);
x_41 = l_Lean_maxRecDepth;
x_42 = l_Lean_Option_get___redArg(x_14, x_31, x_41);
x_43 = lean_ctor_get(x_35, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_35, 6);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 7);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 8);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 9);
lean_inc(x_47);
x_48 = lean_ctor_get(x_35, 10);
lean_inc(x_48);
x_49 = lean_ctor_get(x_35, 11);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_35, sizeof(void*)*13 + 1);
x_51 = lean_ctor_get(x_35, 12);
lean_inc(x_51);
lean_dec(x_35);
lean_inc(x_31);
x_52 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_39);
lean_ctor_set(x_52, 2, x_31);
lean_ctor_set(x_52, 3, x_40);
lean_ctor_set(x_52, 4, x_42);
lean_ctor_set(x_52, 5, x_43);
lean_ctor_set(x_52, 6, x_44);
lean_ctor_set(x_52, 7, x_45);
lean_ctor_set(x_52, 8, x_46);
lean_ctor_set(x_52, 9, x_47);
lean_ctor_set(x_52, 10, x_48);
lean_ctor_set(x_52, 11, x_49);
lean_ctor_set(x_52, 12, x_51);
x_53 = lean_unbox(x_34);
lean_dec(x_34);
lean_ctor_set_uint8(x_52, sizeof(void*)*13, x_53);
lean_ctor_set_uint8(x_52, sizeof(void*)*13 + 1, x_50);
x_54 = lean_apply_3(x_2, x_52, x_36, x_37);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_get(x_7, x_56);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_dec(x_7);
return x_54;
}
}
block_98:
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_st_ref_take(x_7, x_17);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_34);
x_69 = l_Lean_Kernel_enableDiag(x_67, x_68);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 3);
lean_inc(x_72);
x_73 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_inc(x_74);
lean_ctor_set(x_63, 1, x_74);
lean_ctor_set(x_63, 0, x_74);
x_75 = lean_ctor_get(x_65, 5);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 6);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 7);
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set(x_78, 4, x_63);
lean_ctor_set(x_78, 5, x_75);
lean_ctor_set(x_78, 6, x_76);
lean_ctor_set(x_78, 7, x_77);
x_79 = lean_st_ref_set(x_7, x_78, x_66);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_inc(x_7);
x_35 = x_32;
x_36 = x_7;
x_37 = x_80;
goto block_62;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_81 = lean_ctor_get(x_63, 0);
x_82 = lean_ctor_get(x_63, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_63);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_34);
x_85 = l_Lean_Kernel_enableDiag(x_83, x_84);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 3);
lean_inc(x_88);
x_89 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_inc(x_90);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_ctor_get(x_81, 5);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 6);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 7);
lean_inc(x_94);
lean_dec(x_81);
x_95 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_87);
lean_ctor_set(x_95, 3, x_88);
lean_ctor_set(x_95, 4, x_91);
lean_ctor_set(x_95, 5, x_92);
lean_ctor_set(x_95, 6, x_93);
lean_ctor_set(x_95, 7, x_94);
x_96 = lean_st_ref_set(x_7, x_95, x_82);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
lean_inc(x_7);
x_35 = x_32;
x_36 = x_7;
x_37 = x_97;
goto block_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_CoreM_run_x27___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_run_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_CoreM_run_x27(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_113; uint8_t x_114; 
x_5 = lean_io_get_num_heartbeats(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_mk_ref(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_inheritedTraceOptions;
x_12 = lean_st_ref_get(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_KVMap_instValueBool;
x_16 = l_Lean_KVMap_instValueNat;
x_17 = lean_st_ref_get(x_9, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = lean_ctor_get(x_2, 5);
x_26 = lean_ctor_get(x_2, 6);
x_27 = lean_ctor_get(x_2, 7);
x_28 = lean_ctor_get(x_2, 9);
x_29 = lean_ctor_get(x_2, 10);
x_30 = lean_ctor_get(x_2, 11);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_32 = l_Lean_diagnostics;
x_33 = l_Lean_Option_get___redArg(x_15, x_23, x_32);
x_113 = lean_ctor_get(x_18, 0);
lean_inc(x_113);
lean_dec(x_18);
x_114 = l_Lean_Kernel_isDiagnosticsEnabled(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = lean_unbox(x_33);
if (x_115 == 0)
{
lean_inc(x_9);
x_34 = x_9;
x_35 = x_19;
goto block_76;
}
else
{
goto block_112;
}
}
else
{
uint8_t x_116; 
x_116 = lean_unbox(x_33);
if (x_116 == 0)
{
goto block_112;
}
else
{
lean_inc(x_9);
x_34 = x_9;
x_35 = x_19;
goto block_76;
}
}
block_76:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = l_Lean_maxRecDepth;
x_37 = l_Lean_Option_get___redArg(x_16, x_23, x_36);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_38 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_38, 2, x_23);
lean_ctor_set(x_38, 3, x_24);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_25);
lean_ctor_set(x_38, 6, x_26);
lean_ctor_set(x_38, 7, x_27);
lean_ctor_set(x_38, 8, x_6);
lean_ctor_set(x_38, 9, x_28);
lean_ctor_set(x_38, 10, x_29);
lean_ctor_set(x_38, 11, x_30);
lean_ctor_set(x_38, 12, x_13);
x_39 = lean_unbox(x_33);
lean_dec(x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*13, x_39);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 1, x_31);
x_40 = lean_apply_3(x_1, x_38, x_34, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_9, x_42);
lean_dec(x_9);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
if (lean_is_scalar(x_20)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_20;
}
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
if (lean_is_scalar(x_20)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_20;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_20);
lean_dec(x_9);
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_MessageData_toString(x_53, x_52);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_40);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_40, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
lean_dec(x_51);
x_65 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_66 = l___private_Init_Data_Repr_0__Nat_reprFast(x_64);
x_67 = lean_string_append(x_65, x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_40, 0, x_68);
return x_40;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_40, 1);
lean_inc(x_69);
lean_dec(x_40);
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
lean_dec(x_51);
x_71 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_72 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
return x_75;
}
}
}
}
block_112:
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_st_ref_take(x_9, x_19);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_33);
x_83 = l_Lean_Kernel_enableDiag(x_81, x_82);
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 3);
lean_inc(x_86);
x_87 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_inc(x_88);
lean_ctor_set(x_77, 1, x_88);
lean_ctor_set(x_77, 0, x_88);
x_89 = lean_ctor_get(x_79, 5);
lean_inc(x_89);
x_90 = lean_ctor_get(x_79, 6);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 7);
lean_inc(x_91);
lean_dec(x_79);
x_92 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_92, 2, x_85);
lean_ctor_set(x_92, 3, x_86);
lean_ctor_set(x_92, 4, x_77);
lean_ctor_set(x_92, 5, x_89);
lean_ctor_set(x_92, 6, x_90);
lean_ctor_set(x_92, 7, x_91);
x_93 = lean_st_ref_set(x_9, x_92, x_80);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_9);
x_34 = x_9;
x_35 = x_94;
goto block_76;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_33);
x_99 = l_Lean_Kernel_enableDiag(x_97, x_98);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 3);
lean_inc(x_102);
x_103 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
lean_inc(x_104);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_ctor_get(x_95, 5);
lean_inc(x_106);
x_107 = lean_ctor_get(x_95, 6);
lean_inc(x_107);
x_108 = lean_ctor_get(x_95, 7);
lean_inc(x_108);
lean_dec(x_95);
x_109 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_101);
lean_ctor_set(x_109, 3, x_102);
lean_ctor_set(x_109, 4, x_105);
lean_ctor_set(x_109, 5, x_106);
lean_ctor_set(x_109, 6, x_107);
lean_ctor_set(x_109, 7, x_108);
x_110 = lean_st_ref_set(x_9, x_109, x_96);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
lean_inc(x_9);
x_34 = x_9;
x_35 = x_111;
goto block_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_130; uint8_t x_131; 
x_6 = lean_io_get_num_heartbeats(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_mk_ref(x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_inheritedTraceOptions;
x_13 = lean_st_ref_get(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_KVMap_instValueBool;
x_17 = l_Lean_KVMap_instValueNat;
x_18 = lean_st_ref_get(x_10, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 7);
x_30 = lean_ctor_get(x_3, 9);
x_31 = lean_ctor_get(x_3, 10);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*13);
x_33 = lean_ctor_get(x_3, 11);
x_34 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_35 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_25);
lean_ctor_set(x_35, 4, x_26);
lean_ctor_set(x_35, 5, x_27);
lean_ctor_set(x_35, 6, x_28);
lean_ctor_set(x_35, 7, x_29);
lean_ctor_set(x_35, 8, x_7);
lean_ctor_set(x_35, 9, x_30);
lean_ctor_set(x_35, 10, x_31);
lean_ctor_set(x_35, 11, x_33);
lean_ctor_set(x_35, 12, x_14);
lean_ctor_set_uint8(x_35, sizeof(void*)*13, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*13 + 1, x_34);
x_36 = l_Lean_diagnostics;
x_37 = l_Lean_Option_get___redArg(x_16, x_24, x_36);
x_130 = lean_ctor_get(x_19, 0);
lean_inc(x_130);
lean_dec(x_19);
x_131 = l_Lean_Kernel_isDiagnosticsEnabled(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = lean_unbox(x_37);
if (x_132 == 0)
{
lean_inc(x_10);
x_38 = x_35;
x_39 = x_10;
x_40 = x_20;
goto block_93;
}
else
{
goto block_129;
}
}
else
{
uint8_t x_133; 
x_133 = lean_unbox(x_37);
if (x_133 == 0)
{
goto block_129;
}
else
{
lean_inc(x_10);
x_38 = x_35;
x_39 = x_10;
x_40 = x_20;
goto block_93;
}
}
block_93:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 3);
lean_inc(x_43);
x_44 = l_Lean_maxRecDepth;
x_45 = l_Lean_Option_get___redArg(x_17, x_24, x_44);
x_46 = lean_ctor_get(x_38, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 7);
lean_inc(x_48);
x_49 = lean_ctor_get(x_38, 8);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 9);
lean_inc(x_50);
x_51 = lean_ctor_get(x_38, 10);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 11);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_38, sizeof(void*)*13 + 1);
x_54 = lean_ctor_get(x_38, 12);
lean_inc(x_54);
lean_dec(x_38);
lean_inc(x_24);
x_55 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_42);
lean_ctor_set(x_55, 2, x_24);
lean_ctor_set(x_55, 3, x_43);
lean_ctor_set(x_55, 4, x_45);
lean_ctor_set(x_55, 5, x_46);
lean_ctor_set(x_55, 6, x_47);
lean_ctor_set(x_55, 7, x_48);
lean_ctor_set(x_55, 8, x_49);
lean_ctor_set(x_55, 9, x_50);
lean_ctor_set(x_55, 10, x_51);
lean_ctor_set(x_55, 11, x_52);
lean_ctor_set(x_55, 12, x_54);
x_56 = lean_unbox(x_37);
lean_dec(x_37);
lean_ctor_set_uint8(x_55, sizeof(void*)*13, x_56);
lean_ctor_set_uint8(x_55, sizeof(void*)*13 + 1, x_53);
x_57 = lean_apply_3(x_2, x_55, x_39, x_40);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_st_ref_get(x_10, x_59);
lean_dec(x_10);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
if (lean_is_scalar(x_21)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_21;
}
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
if (lean_is_scalar(x_21)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_21;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; 
lean_dec(x_21);
lean_dec(x_10);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_dec(x_57);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_MessageData_toString(x_70, x_69);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_71);
x_77 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_77, 0, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_57);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_57, 0);
lean_dec(x_80);
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
lean_dec(x_68);
x_82 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_83 = l___private_Init_Data_Repr_0__Nat_reprFast(x_81);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_57, 0, x_85);
return x_57;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_57, 1);
lean_inc(x_86);
lean_dec(x_57);
x_87 = lean_ctor_get(x_68, 0);
lean_inc(x_87);
lean_dec(x_68);
x_88 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_89 = l___private_Init_Data_Repr_0__Nat_reprFast(x_87);
x_90 = lean_string_append(x_88, x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_86);
return x_92;
}
}
}
}
block_129:
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_st_ref_take(x_10, x_20);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_37);
x_100 = l_Lean_Kernel_enableDiag(x_98, x_99);
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 3);
lean_inc(x_103);
x_104 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_inc(x_105);
lean_ctor_set(x_94, 1, x_105);
lean_ctor_set(x_94, 0, x_105);
x_106 = lean_ctor_get(x_96, 5);
lean_inc(x_106);
x_107 = lean_ctor_get(x_96, 6);
lean_inc(x_107);
x_108 = lean_ctor_get(x_96, 7);
lean_inc(x_108);
lean_dec(x_96);
x_109 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_102);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set(x_109, 4, x_94);
lean_ctor_set(x_109, 5, x_106);
lean_ctor_set(x_109, 6, x_107);
lean_ctor_set(x_109, 7, x_108);
x_110 = lean_st_ref_set(x_10, x_109, x_97);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
lean_inc(x_10);
x_38 = x_35;
x_39 = x_10;
x_40 = x_111;
goto block_93;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_112 = lean_ctor_get(x_94, 0);
x_113 = lean_ctor_get(x_94, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_94);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_37);
x_116 = l_Lean_Kernel_enableDiag(x_114, x_115);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 3);
lean_inc(x_119);
x_120 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_inc(x_121);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_ctor_get(x_112, 5);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 6);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 7);
lean_inc(x_125);
lean_dec(x_112);
x_126 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_126, 0, x_116);
lean_ctor_set(x_126, 1, x_117);
lean_ctor_set(x_126, 2, x_118);
lean_ctor_set(x_126, 3, x_119);
lean_ctor_set(x_126, 4, x_122);
lean_ctor_set(x_126, 5, x_123);
lean_ctor_set(x_126, 6, x_124);
lean_ctor_set(x_126, 7, x_125);
x_127 = lean_st_ref_set(x_10, x_126, x_113);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
lean_inc(x_10);
x_38 = x_35;
x_39 = x_10;
x_40 = x_128;
goto block_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_CoreM_toIO___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_toIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_CoreM_toIO(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = l_EStateM_nonBacktrackable(lean_box(0));
x_8 = lean_alloc_closure((void*)(l_EStateM_tryCatch), 8, 7);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, lean_box(0));
lean_closure_set(x_8, 3, x_7);
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_6);
lean_closure_set(x_8, 6, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_EStateM_throw), 5, 4);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, lean_box(0));
lean_closure_set(x_4, 3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 8);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 10);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_22 = lean_ctor_get(x_4, 11);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_24 = lean_ctor_get(x_4, 12);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_14);
lean_ctor_set(x_25, 3, x_11);
lean_ctor_set(x_25, 4, x_8);
lean_ctor_set(x_25, 5, x_15);
lean_ctor_set(x_25, 6, x_16);
lean_ctor_set(x_25, 7, x_17);
lean_ctor_set(x_25, 8, x_18);
lean_ctor_set(x_25, 9, x_19);
lean_ctor_set(x_25, 10, x_20);
lean_ctor_set(x_25, 11, x_22);
lean_ctor_set(x_25, 12, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*13, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*13 + 1, x_23);
x_26 = lean_apply_5(x_3, lean_box(0), x_1, x_25, x_5, x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_ctor_get(x_4, 5);
lean_inc(x_27);
x_28 = l_Lean_throwMaxRecDepthAt___redArg(x_2, x_27);
x_29 = lean_apply_3(x_28, x_4, x_5, x_6);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_4 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__1), 4, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__2___boxed), 3, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_8 = l_instMonadEIO(lean_box(0));
x_9 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, lean_box(0));
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_4);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Core_instMonadRefCoreM;
x_31 = l_Lean_Core_instAddMessageContextCoreM;
x_32 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(lean_box(0), x_31, x_25);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__3), 6, 2);
lean_closure_set(x_34, 0, x_3);
lean_closure_set(x_34, 1, x_33);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_apply_2(x_36, lean_box(0), x_34);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_apply_1(x_38, lean_box(0));
x_40 = lean_apply_4(x_35, lean_box(0), lean_box(0), x_37, x_39);
return x_40;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withIncRecDepth___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_withIncRecDepth___redArg___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkInterrupted(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_6 = l_instMonadEIO(lean_box(0));
x_7 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, lean_box(0));
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
x_24 = lean_ctor_get(x_1, 11);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_IO_CancelToken_isSet(x_27, x_3);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__2___boxed), 3, 0);
x_39 = lean_alloc_closure((void*)(l_Lean_Core_withIncRecDepth___redArg___lam__1), 4, 0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_40);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Core_instMonadRefCoreM;
x_45 = l_Lean_Core_instAddMessageContextCoreM;
x_46 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(lean_box(0), x_45, x_23);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_Lean_throwInterruptException___redArg(x_47);
x_49 = lean_apply_3(x_48, x_1, x_2, x_37);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("debug", 5, 5);
x_3 = lean_mk_string_unchecked("moduleNameAtTimeout", 19, 19);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_mk_string_unchecked("include module name in deterministic timeout error messages.\nRemark: we set this option to false to increase the stability of our test suite", 140, 140);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Core", 4, 4);
x_10 = l_Lean_Name_mkStr4(x_8, x_9, x_2, x_3);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_4, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Core_throwMaxHeartbeat___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_4, 2);
x_42 = l_Lean_Core_debug_moduleNameAtTimeout;
x_43 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_1);
x_44 = lean_mk_string_unchecked("", 0, 0);
x_6 = x_44;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_alloc_closure((void*)(l_Lean_Core_throwMaxHeartbeat___redArg___lam__0___boxed), 1, 0);
x_46 = lean_mk_string_unchecked(" at `", 5, 5);
x_47 = l_Lean_Name_toString(x_1, x_43, x_45);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("`", 1, 1);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
x_6 = x_50;
goto block_40;
}
block_40:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_mk_string_unchecked("runtime", 7, 7);
x_9 = lean_mk_string_unchecked("maxHeartbeats", 13, 13);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = lean_mk_string_unchecked("(deterministic) timeout", 23, 23);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_stringToMessageData(x_6);
lean_dec(x_6);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked(", maximum number of heartbeats (", 32, 32);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_unsigned_to_nat(1000u);
x_19 = lean_nat_div(x_3, x_18);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked(") has been reached\nUse `set_option ", 35, 35);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofName(x_2);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked(" <num>` to set the limit.", 25, 25);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_useDiagnosticMsg;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("", 0, 0);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_throwMaxHeartbeat___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Core_throwMaxHeartbeat___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_throwMaxHeartbeat___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_throwMaxHeartbeat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_throwMaxHeartbeat(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_io_get_num_heartbeats(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_4, 8);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_8);
x_16 = lean_box(0);
x_17 = l_Lean_Name_str___override(x_16, x_1);
x_18 = l_Lean_Core_throwMaxHeartbeat___redArg(x_17, x_2, x_3, x_4, x_11);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_ctor_get(x_4, 8);
x_22 = lean_nat_sub(x_19, x_21);
lean_dec(x_19);
x_23 = lean_nat_dec_lt(x_3, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = l_Lean_Name_str___override(x_26, x_1);
x_28 = l_Lean_Core_throwMaxHeartbeat___redArg(x_27, x_2, x_3, x_4, x_20);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeatsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_checkMaxHeartbeatsCore(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_mk_string_unchecked("maxHeartbeats", 13, 13);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_ctor_get(x_2, 9);
x_7 = l_Lean_Core_checkMaxHeartbeatsCore___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkMaxHeartbeats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkMaxHeartbeats(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_interruptExceptionId;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 11);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_IO_CancelToken_isSet(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Core_checkMaxHeartbeats___redArg(x_1, x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_checkSystem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_checkSystem(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_io_get_num_heartbeats(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_19 = lean_ctor_get(x_2, 11);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_21 = lean_ctor_get(x_2, 12);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_9);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_11);
lean_ctor_set(x_22, 4, x_12);
lean_ctor_set(x_22, 5, x_13);
lean_ctor_set(x_22, 6, x_14);
lean_ctor_set(x_22, 7, x_15);
lean_ctor_set(x_22, 8, x_6);
lean_ctor_set(x_22, 9, x_16);
lean_ctor_set(x_22, 10, x_17);
lean_ctor_set(x_22, 11, x_19);
lean_ctor_set(x_22, 12, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*13, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*13 + 1, x_20);
x_23 = lean_apply_3(x_1, x_22, x_3, x_7);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_2, lean_box(0), x_1);
x_7 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_8, lean_box(0));
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 7);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_1);
lean_ctor_set(x_14, 6, x_12);
lean_ctor_set(x_14, 7, x_13);
x_15 = lean_st_ref_set(x_2, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_setMessageLog___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_setMessageLog___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_setMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_setMessageLog(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_unsigned_to_nat(5u);
x_5 = lean_usize_of_nat(x_4);
x_6 = lean_usize_to_nat(x_5);
x_7 = lean_nat_pow(x_3, x_6);
lean_dec(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set_usize(x_13, 4, x_5);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Lean_Core_setMessageLog___redArg(x_15, x_1, x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_resetMessageLog___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_resetMessageLog___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_resetMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_resetMessageLog(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 5);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 5);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getMessageLog___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getMessageLog___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getMessageLog(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
lean_inc(x_6);
x_12 = l_Lean_MessageLog_markAllReported(x_6);
x_13 = lean_ctor_get(x_4, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 7);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
lean_ctor_set(x_15, 6, x_13);
lean_ctor_set(x_15, 7, x_14);
x_16 = lean_st_ref_set(x_1, x_15, x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptyMessageLog___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getAndEmptyMessageLog___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptyMessageLog___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptyMessageLog(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 6);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_9);
lean_ctor_set(x_15, 4, x_10);
lean_ctor_set(x_15, 5, x_11);
lean_ctor_set(x_15, 6, x_12);
lean_ctor_set(x_15, 7, x_14);
x_16 = lean_st_ref_set(x_1, x_15, x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_4, 7);
lean_inc(x_19);
lean_dec(x_4);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_4, 7);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptySnapshotTasks___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_getAndEmptySnapshotTasks___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_getAndEmptySnapshotTasks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_getAndEmptySnapshotTasks(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 5);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_MessageLog_hasErrors(x_7);
lean_dec(x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 5);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_MessageLog_hasErrors(x_12);
lean_dec(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Core_instMonadLogCoreM___lam__3(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_27; uint8_t x_28; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_27 = lean_mk_string_unchecked("trace", 5, 5);
x_28 = lean_string_dec_eq(x_5, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = lean_unbox(x_3);
x_6 = x_29;
goto block_26;
}
else
{
x_6 = x_1;
goto block_26;
}
block_26:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_mk_string_unchecked("Tactic", 6, 6);
x_12 = lean_string_dec_eq(x_8, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_13; 
x_13 = lean_unbox(x_3);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_unbox(x_3);
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
x_16 = lean_string_dec_eq(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_17; 
x_17 = lean_unbox(x_3);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_unbox(x_3);
return x_18;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
return x_1;
}
else
{
uint8_t x_19; 
x_19 = lean_unbox(x_3);
return x_19;
}
}
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
x_21 = lean_string_dec_eq(x_5, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_22; 
x_22 = lean_unbox(x_3);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_unbox(x_3);
return x_23;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
return x_1;
}
else
{
uint8_t x_24; 
x_24 = lean_unbox(x_3);
return x_24;
}
}
}
}
default: 
{
uint8_t x_25; 
x_25 = lean_unbox(x_3);
return x_25;
}
}
}
}
else
{
uint8_t x_30; 
x_30 = lean_unbox(x_3);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_67; 
x_67 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
if (x_67 == 0)
{
goto block_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_box(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__3___boxed), 2, 1);
lean_closure_set(x_69, 0, x_68);
x_70 = lean_ctor_get(x_1, 4);
lean_inc(x_70);
x_71 = l_Lean_MessageData_hasTag(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_4);
return x_73;
}
else
{
goto block_66;
}
}
block_66:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 6);
x_6 = lean_ctor_get(x_2, 7);
x_7 = lean_st_ref_take(x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_5);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_11);
x_20 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 1, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 2, x_17);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_9, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_9, 5);
lean_inc(x_26);
x_27 = l_Lean_MessageLog_add(x_20, x_26);
x_28 = lean_ctor_get(x_9, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_9, 7);
lean_inc(x_29);
lean_dec(x_9);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set(x_30, 6, x_28);
lean_ctor_set(x_30, 7, x_29);
x_31 = lean_st_ref_set(x_3, x_30, x_10);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_6);
x_41 = lean_ctor_get(x_1, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_46 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_41);
x_50 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*5, x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*5 + 1, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*5 + 2, x_47);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_38, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_38, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_38, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_38, 5);
lean_inc(x_56);
x_57 = l_Lean_MessageLog_add(x_50, x_56);
x_58 = lean_ctor_get(x_38, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_38, 7);
lean_inc(x_59);
lean_dec(x_38);
x_60 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set(x_60, 3, x_54);
lean_ctor_set(x_60, 4, x_55);
lean_ctor_set(x_60, 5, x_57);
lean_ctor_set(x_60, 6, x_58);
lean_ctor_set(x_60, 7, x_59);
x_61 = lean_st_ref_set(x_3, x_60, x_39);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
}
}
static lean_object* _init_l_Lean_Core_instMonadLogCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_instMonadRefCoreM___lam__0___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__2___boxed), 3, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__1___boxed), 3, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instMonadLogCoreM___lam__4___boxed), 4, 0);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_instMonadLogCoreM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Core_instMonadLogCoreM___lam__3(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_instMonadLogCoreM___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_instMonadLogCoreM___lam__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 7);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_push(x_14, x_1);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_10);
lean_ctor_set(x_16, 4, x_11);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_16, 6, x_13);
lean_ctor_set(x_16, 7, x_15);
x_17 = lean_st_ref_set(x_2, x_16, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_logSnapshotTask___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_logSnapshotTask___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_logSnapshotTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_logSnapshotTask(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
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
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_IO_addHeartbeats(x_1, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_4(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_79; uint8_t x_80; 
x_18 = lean_st_mk_ref(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_inheritedTraceOptions;
x_22 = lean_st_ref_get(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_19, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_3);
lean_closure_set(x_28, 2, x_16);
x_29 = l_Lean_diagnostics;
x_30 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_4, x_29);
x_79 = lean_ctor_get(x_26, 0);
lean_inc(x_79);
lean_dec(x_26);
x_80 = l_Lean_Kernel_isDiagnosticsEnabled(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
if (x_30 == 0)
{
lean_inc(x_19);
x_31 = x_19;
x_32 = x_27;
goto block_44;
}
else
{
goto block_78;
}
}
else
{
if (x_30 == 0)
{
goto block_78;
}
else
{
lean_inc(x_19);
x_31 = x_19;
x_32 = x_27;
goto block_44;
}
}
block_44:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l_Lean_maxRecDepth;
x_34 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_4, x_33);
x_35 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_6);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_7);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_8);
lean_ctor_set(x_35, 6, x_9);
lean_ctor_set(x_35, 7, x_10);
lean_ctor_set(x_35, 8, x_11);
lean_ctor_set(x_35, 9, x_12);
lean_ctor_set(x_35, 10, x_13);
lean_ctor_set(x_35, 11, x_14);
lean_ctor_set(x_35, 12, x_23);
lean_ctor_set_uint8(x_35, sizeof(void*)*13, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*13 + 1, x_15);
x_36 = l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(x_28, x_35, x_31, x_32);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_19, x_38);
lean_dec(x_19);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_dec(x_19);
return x_36;
}
}
block_78:
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_st_ref_take(x_19, x_27);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = l_Lean_Kernel_enableDiag(x_49, x_30);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 3);
lean_inc(x_53);
x_54 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_inc(x_55);
lean_ctor_set(x_45, 1, x_55);
lean_ctor_set(x_45, 0, x_55);
x_56 = lean_ctor_get(x_47, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_47, 6);
lean_inc(x_57);
x_58 = lean_ctor_get(x_47, 7);
lean_inc(x_58);
lean_dec(x_47);
x_59 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_52);
lean_ctor_set(x_59, 3, x_53);
lean_ctor_set(x_59, 4, x_45);
lean_ctor_set(x_59, 5, x_56);
lean_ctor_set(x_59, 6, x_57);
lean_ctor_set(x_59, 7, x_58);
x_60 = lean_st_ref_set(x_19, x_59, x_48);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_19);
x_31 = x_19;
x_32 = x_61;
goto block_44;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_62 = lean_ctor_get(x_45, 0);
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_45);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = l_Lean_Kernel_enableDiag(x_64, x_30);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 3);
lean_inc(x_68);
x_69 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_inc(x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_ctor_get(x_62, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 6);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 7);
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_67);
lean_ctor_set(x_75, 3, x_68);
lean_ctor_set(x_75, 4, x_71);
lean_ctor_set(x_75, 5, x_72);
lean_ctor_set(x_75, 6, x_73);
lean_ctor_set(x_75, 7, x_74);
x_76 = lean_st_ref_set(x_19, x_75, x_63);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_19);
x_31 = x_19;
x_32 = x_77;
goto block_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_get_num_heartbeats(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 10);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
lean_dec(x_3);
x_23 = lean_nat_sub(x_11, x_19);
lean_dec(x_11);
x_24 = lean_box(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 17, 15);
lean_closure_set(x_25, 0, x_7);
lean_closure_set(x_25, 1, x_23);
lean_closure_set(x_25, 2, x_1);
lean_closure_set(x_25, 3, x_14);
lean_closure_set(x_25, 4, x_12);
lean_closure_set(x_25, 5, x_13);
lean_closure_set(x_25, 6, x_15);
lean_closure_set(x_25, 7, x_16);
lean_closure_set(x_25, 8, x_17);
lean_closure_set(x_25, 9, x_18);
lean_closure_set(x_25, 10, x_19);
lean_closure_set(x_25, 11, x_20);
lean_closure_set(x_25, 12, x_21);
lean_closure_set(x_25, 13, x_2);
lean_closure_set(x_25, 14, x_24);
lean_ctor_set(x_9, 0, x_25);
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 7);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 8);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 9);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 10);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
lean_dec(x_3);
x_39 = lean_nat_sub(x_26, x_35);
lean_dec(x_26);
x_40 = lean_box(x_38);
x_41 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsync___redArg___lam__1___boxed), 17, 15);
lean_closure_set(x_41, 0, x_7);
lean_closure_set(x_41, 1, x_39);
lean_closure_set(x_41, 2, x_1);
lean_closure_set(x_41, 3, x_30);
lean_closure_set(x_41, 4, x_28);
lean_closure_set(x_41, 5, x_29);
lean_closure_set(x_41, 6, x_31);
lean_closure_set(x_41, 7, x_32);
lean_closure_set(x_41, 8, x_33);
lean_closure_set(x_41, 9, x_34);
lean_closure_set(x_41, 10, x_35);
lean_closure_set(x_41, 11, x_36);
lean_closure_set(x_41, 12, x_37);
lean_closure_set(x_41, 13, x_2);
lean_closure_set(x_41, 14, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsync___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_withCurrHeartbeats___at___Lean_Core_wrapAsync_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsync___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___lam__1___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_15);
lean_dec(x_15);
x_19 = l_Lean_Core_wrapAsync___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_18, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsync___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsync(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_mk_string_unchecked("stderrAsMessages", 16, 16);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(1);
x_5 = lean_mk_string_unchecked("server", 6, 6);
x_6 = lean_mk_string_unchecked("(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message", 133, 133);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Core", 4, 4);
x_10 = l_Lean_Name_mkStr3(x_8, x_9, x_2);
x_11 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_3, x_7, x_10, x_1);
lean_dec(x_7);
return x_11;
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_3975_() {
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
LEAN_EXPORT lean_object* l_Lean_Core_mkSnapshot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_3, 5);
lean_inc(x_29);
x_30 = lean_string_utf8_byte_size(x_1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_instDecidableEqPos(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_46; lean_object* x_47; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_46 = lean_ctor_get(x_2, 5);
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Lean_Syntax_getPos_x3f(x_46, x_32);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
x_35 = x_31;
goto block_45;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_35 = x_48;
goto block_45;
}
block_45:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_36 = l_Lean_FileMap_toPosition(x_34, x_35);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_mk_string_unchecked("", 0, 0);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_1);
x_41 = l_Lean_MessageData_ofFormat(x_40);
x_42 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*5, x_32);
x_43 = lean_unbox(x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*5 + 1, x_43);
lean_ctor_set_uint8(x_42, sizeof(void*)*5 + 2, x_32);
x_44 = l_Lean_MessageLog_add(x_42, x_29);
x_6 = x_44;
x_7 = x_5;
goto block_28;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_29;
x_7 = x_5;
goto block_28;
}
block_28:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_15);
x_16 = lean_ctor_get(x_3, 7);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_box(0);
x_21 = lean_ctor_get(x_3, 3);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_24);
x_25 = lean_ctor_get(x_3, 7);
lean_inc(x_25);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
}
}
static lean_object* _init_l___auto____x40_Lean_CoreM___hyg_4116_() {
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
lean_free_object(x_4);
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 3);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_to_nat(x_16);
x_18 = lean_nat_pow(x_14, x_17);
lean_dec(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = lean_usize_to_nat(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_usize(x_24, 4, x_16);
x_25 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint64(x_25, sizeof(void*)*1, x_13);
x_26 = lean_ctor_get(x_7, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 7);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_11);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set(x_30, 6, x_28);
lean_ctor_set(x_30, 7, x_29);
x_31 = lean_st_ref_set(x_1, x_30, x_8);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 3);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_4, 3);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_instDecidableEqPos(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = l_instDecidableEqPos(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_instDecidableEqPos(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = l_instDecidableEqPos(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
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
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
x_10 = lean_uint64_of_nat(x_7);
lean_dec(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_sub(x_21, x_23);
x_25 = lean_usize_land(x_20, x_24);
x_26 = lean_array_uget(x_1, x_25);
lean_ctor_set(x_2, 2, x_26);
x_27 = lean_array_uset(x_1, x_25, x_2);
x_1 = x_27;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
x_34 = lean_array_get_size(x_1);
x_35 = lean_uint64_of_nat(x_32);
lean_dec(x_32);
x_36 = lean_uint64_of_nat(x_33);
lean_dec(x_33);
x_37 = lean_uint64_mix_hash(x_35, x_36);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_1, x_51);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_29);
lean_ctor_set(x_53, 1, x_30);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_array_uset(x_1, x_51, x_53);
x_1 = x_54;
x_2 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4_spec__4___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4_spec__4___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
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
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = l_instDecidableEqPos(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = l_instDecidableEqPos(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(1, 3, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(1, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_3, x_5);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
lean_inc(x_13);
x_14 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_2, x_12, x_13, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_dec(x_13);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
x_6 = x_27;
x_9 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_107; 
x_10 = lean_box(0);
x_17 = lean_array_uget(x_2, x_4);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_100 = lean_ctor_get(x_6, 5);
x_101 = lean_ctor_get(x_17, 0);
lean_inc(x_101);
x_102 = l_Lean_replaceRef(x_101, x_100);
lean_dec(x_101);
x_107 = l_Lean_Syntax_getPos_x3f(x_102, x_1);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_unsigned_to_nat(0u);
x_103 = x_108;
goto block_106;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_103 = x_109;
goto block_106;
}
block_16:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_usize_add(x_4, x_11);
x_4 = x_14;
x_5 = x_13;
goto _start;
}
block_99:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; lean_object* x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_array_get_size(x_21);
x_25 = lean_uint64_of_nat(x_19);
x_26 = lean_uint64_of_nat(x_20);
x_27 = lean_uint64_mix_hash(x_25, x_26);
x_28 = lean_unsigned_to_nat(32u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_unsigned_to_nat(16u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_usize_of_nat(x_38);
x_40 = lean_usize_sub(x_37, x_39);
x_41 = lean_usize_land(x_36, x_40);
x_42 = lean_array_uget(x_21, x_41);
lean_dec(x_21);
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; uint8_t x_57; 
x_46 = lean_ctor_get(x_18, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_18, 0);
lean_dec(x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_20);
x_49 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_48, x_23, x_42);
lean_dec(x_42);
lean_dec(x_23);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_dec(x_17);
x_51 = lean_array_push(x_49, x_50);
x_52 = lean_array_get_size(x_44);
x_53 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_54 = lean_usize_sub(x_53, x_39);
x_55 = lean_usize_land(x_36, x_54);
x_56 = lean_array_uget(x_44, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_48, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_nat_add(x_43, x_38);
lean_dec(x_43);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_56);
x_60 = lean_array_uset(x_44, x_55, x_59);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_nat_shiftl(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_60);
lean_ctor_set(x_18, 1, x_67);
lean_ctor_set(x_18, 0, x_58);
x_11 = x_39;
x_12 = x_18;
goto block_16;
}
else
{
lean_ctor_set(x_18, 1, x_60);
lean_ctor_set(x_18, 0, x_58);
x_11 = x_39;
x_12 = x_18;
goto block_16;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_box(0);
x_69 = lean_array_uset(x_44, x_55, x_68);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_48, x_51, x_56);
x_71 = lean_array_uset(x_69, x_55, x_70);
lean_ctor_set(x_18, 1, x_71);
x_11 = x_39;
x_12 = x_18;
goto block_16;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_18);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_19);
lean_ctor_set(x_72, 1, x_20);
x_73 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_72, x_23, x_42);
lean_dec(x_42);
lean_dec(x_23);
x_74 = lean_ctor_get(x_17, 1);
lean_inc(x_74);
lean_dec(x_17);
x_75 = lean_array_push(x_73, x_74);
x_76 = lean_array_get_size(x_44);
x_77 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_78 = lean_usize_sub(x_77, x_39);
x_79 = lean_usize_land(x_36, x_78);
x_80 = lean_array_uget(x_44, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_72, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_nat_add(x_43, x_38);
lean_dec(x_43);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_75);
lean_ctor_set(x_83, 2, x_80);
x_84 = lean_array_uset(x_44, x_79, x_83);
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
lean_object* x_91; lean_object* x_92; 
x_91 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_84);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_91);
x_11 = x_39;
x_12 = x_92;
goto block_16;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_84);
x_11 = x_39;
x_12 = x_93;
goto block_16;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_box(0);
x_95 = lean_array_uset(x_44, x_79, x_94);
x_96 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_72, x_75, x_80);
x_97 = lean_array_uset(x_95, x_79, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_43);
lean_ctor_set(x_98, 1, x_97);
x_11 = x_39;
x_12 = x_98;
goto block_16;
}
}
}
block_106:
{
lean_object* x_104; 
x_104 = l_Lean_Syntax_getTailPos_x3f(x_102, x_1);
lean_dec(x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_inc(x_103);
x_19 = x_103;
x_20 = x_103;
goto block_99;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec(x_104);
x_19 = x_103;
x_20 = x_105;
goto block_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_108; 
x_11 = lean_box(0);
x_18 = lean_array_uget(x_2, x_4);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_101 = lean_ctor_get(x_6, 5);
x_102 = lean_ctor_get(x_18, 0);
lean_inc(x_102);
x_103 = l_Lean_replaceRef(x_102, x_101);
lean_dec(x_102);
x_108 = l_Lean_Syntax_getPos_x3f(x_103, x_1);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_unsigned_to_nat(0u);
x_104 = x_109;
goto block_107;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_104 = x_110;
goto block_107;
}
block_17:
{
lean_object* x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_usize_add(x_4, x_12);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(x_1, x_2, x_3, x_15, x_14, x_6, x_8);
return x_16;
}
block_100:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; lean_object* x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_array_get_size(x_22);
x_26 = lean_uint64_of_nat(x_20);
x_27 = lean_uint64_of_nat(x_21);
x_28 = lean_uint64_mix_hash(x_26, x_27);
x_29 = lean_unsigned_to_nat(32u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_unsigned_to_nat(16u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_sub(x_38, x_40);
x_42 = lean_usize_land(x_37, x_41);
x_43 = lean_array_uget(x_22, x_42);
lean_dec(x_22);
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; uint8_t x_58; 
x_47 = lean_ctor_get(x_19, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_19, 0);
lean_dec(x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_20);
lean_ctor_set(x_49, 1, x_21);
x_50 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_49, x_24, x_43);
lean_dec(x_43);
lean_dec(x_24);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_dec(x_18);
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_array_get_size(x_45);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = lean_usize_sub(x_54, x_40);
x_56 = lean_usize_land(x_37, x_55);
x_57 = lean_array_uget(x_45, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_49, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_59 = lean_nat_add(x_44, x_39);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_57);
x_61 = lean_array_uset(x_45, x_56, x_60);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_shiftl(x_59, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_61);
lean_ctor_set(x_19, 1, x_68);
lean_ctor_set(x_19, 0, x_59);
x_12 = x_40;
x_13 = x_19;
goto block_17;
}
else
{
lean_ctor_set(x_19, 1, x_61);
lean_ctor_set(x_19, 0, x_59);
x_12 = x_40;
x_13 = x_19;
goto block_17;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_box(0);
x_70 = lean_array_uset(x_45, x_56, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_49, x_52, x_57);
x_72 = lean_array_uset(x_70, x_56, x_71);
lean_ctor_set(x_19, 1, x_72);
x_12 = x_40;
x_13 = x_19;
goto block_17;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; size_t x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_19);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_20);
lean_ctor_set(x_73, 1, x_21);
x_74 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_73, x_24, x_43);
lean_dec(x_43);
lean_dec(x_24);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_dec(x_18);
x_76 = lean_array_push(x_74, x_75);
x_77 = lean_array_get_size(x_45);
x_78 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_79 = lean_usize_sub(x_78, x_40);
x_80 = lean_usize_land(x_37, x_79);
x_81 = lean_array_uget(x_45, x_80);
x_82 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_73, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_nat_add(x_44, x_39);
lean_dec(x_44);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set(x_84, 2, x_81);
x_85 = lean_array_uset(x_45, x_80, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_nat_shiftl(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_83);
lean_ctor_set(x_93, 1, x_92);
x_12 = x_40;
x_13 = x_93;
goto block_17;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_85);
x_12 = x_40;
x_13 = x_94;
goto block_17;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_box(0);
x_96 = lean_array_uset(x_45, x_80, x_95);
x_97 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_73, x_76, x_81);
x_98 = lean_array_uset(x_96, x_80, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_44);
lean_ctor_set(x_99, 1, x_98);
x_12 = x_40;
x_13 = x_99;
goto block_17;
}
}
}
block_107:
{
lean_object* x_105; 
x_105 = l_Lean_Syntax_getTailPos_x3f(x_103, x_1);
lean_dec(x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_inc(x_104);
x_20 = x_104;
x_21 = x_104;
goto block_100;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
x_20 = x_104;
x_21 = x_106;
goto block_100;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_array_size(x_9);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_1, x_2, x_9, x_12, x_14, x_11, x_5, x_6, x_7);
lean_dec(x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_20);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_free_object(x_3);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
x_33 = lean_array_size(x_30);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_usize_of_nat(x_34);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_1, x_2, x_30, x_33, x_35, x_32, x_5, x_6, x_7);
lean_dec(x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_45 = x_36;
} else {
 lean_dec_ref(x_36);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_4);
x_52 = lean_array_size(x_49);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_usize_of_nat(x_53);
x_55 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_1, x_49, x_52, x_54, x_51, x_5, x_6, x_7);
lean_dec(x_49);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_55, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
lean_ctor_set(x_3, 0, x_60);
lean_ctor_set(x_55, 0, x_3);
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
lean_ctor_set(x_3, 0, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_56);
lean_free_object(x_3);
x_64 = !lean_is_exclusive(x_55);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_55, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_66);
return x_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec(x_57);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; lean_object* x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_3, 0);
lean_inc(x_70);
lean_dec(x_3);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_4);
x_73 = lean_array_size(x_70);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_usize_of_nat(x_74);
x_76 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_1, x_70, x_73, x_75, x_72, x_5, x_6, x_7);
lean_dec(x_70);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_77);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_85 = x_76;
} else {
 lean_dec_ref(x_76);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_78, 0);
lean_inc(x_86);
lean_dec(x_78);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_107; 
x_10 = lean_box(0);
x_17 = lean_array_uget(x_2, x_4);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_100 = lean_ctor_get(x_6, 5);
x_101 = lean_ctor_get(x_17, 0);
lean_inc(x_101);
x_102 = l_Lean_replaceRef(x_101, x_100);
lean_dec(x_101);
x_107 = l_Lean_Syntax_getPos_x3f(x_102, x_1);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_unsigned_to_nat(0u);
x_103 = x_108;
goto block_106;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_103 = x_109;
goto block_106;
}
block_16:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_usize_add(x_4, x_11);
x_4 = x_14;
x_5 = x_13;
goto _start;
}
block_99:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; lean_object* x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_array_get_size(x_21);
x_25 = lean_uint64_of_nat(x_19);
x_26 = lean_uint64_of_nat(x_20);
x_27 = lean_uint64_mix_hash(x_25, x_26);
x_28 = lean_unsigned_to_nat(32u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_unsigned_to_nat(16u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_usize_of_nat(x_38);
x_40 = lean_usize_sub(x_37, x_39);
x_41 = lean_usize_land(x_36, x_40);
x_42 = lean_array_uget(x_21, x_41);
lean_dec(x_21);
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; uint8_t x_57; 
x_46 = lean_ctor_get(x_18, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_18, 0);
lean_dec(x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_19);
lean_ctor_set(x_48, 1, x_20);
x_49 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_48, x_23, x_42);
lean_dec(x_42);
lean_dec(x_23);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_dec(x_17);
x_51 = lean_array_push(x_49, x_50);
x_52 = lean_array_get_size(x_44);
x_53 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_54 = lean_usize_sub(x_53, x_39);
x_55 = lean_usize_land(x_36, x_54);
x_56 = lean_array_uget(x_44, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_48, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_nat_add(x_43, x_38);
lean_dec(x_43);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_56);
x_60 = lean_array_uset(x_44, x_55, x_59);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_nat_shiftl(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_60);
lean_ctor_set(x_18, 1, x_67);
lean_ctor_set(x_18, 0, x_58);
x_11 = x_39;
x_12 = x_18;
goto block_16;
}
else
{
lean_ctor_set(x_18, 1, x_60);
lean_ctor_set(x_18, 0, x_58);
x_11 = x_39;
x_12 = x_18;
goto block_16;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_box(0);
x_69 = lean_array_uset(x_44, x_55, x_68);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_48, x_51, x_56);
x_71 = lean_array_uset(x_69, x_55, x_70);
lean_ctor_set(x_18, 1, x_71);
x_11 = x_39;
x_12 = x_18;
goto block_16;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_18);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_19);
lean_ctor_set(x_72, 1, x_20);
x_73 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_72, x_23, x_42);
lean_dec(x_42);
lean_dec(x_23);
x_74 = lean_ctor_get(x_17, 1);
lean_inc(x_74);
lean_dec(x_17);
x_75 = lean_array_push(x_73, x_74);
x_76 = lean_array_get_size(x_44);
x_77 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_78 = lean_usize_sub(x_77, x_39);
x_79 = lean_usize_land(x_36, x_78);
x_80 = lean_array_uget(x_44, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_72, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_nat_add(x_43, x_38);
lean_dec(x_43);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_75);
lean_ctor_set(x_83, 2, x_80);
x_84 = lean_array_uset(x_44, x_79, x_83);
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
lean_object* x_91; lean_object* x_92; 
x_91 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_84);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_91);
x_11 = x_39;
x_12 = x_92;
goto block_16;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_84);
x_11 = x_39;
x_12 = x_93;
goto block_16;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_box(0);
x_95 = lean_array_uset(x_44, x_79, x_94);
x_96 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_72, x_75, x_80);
x_97 = lean_array_uset(x_95, x_79, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_43);
lean_ctor_set(x_98, 1, x_97);
x_11 = x_39;
x_12 = x_98;
goto block_16;
}
}
}
block_106:
{
lean_object* x_104; 
x_104 = l_Lean_Syntax_getTailPos_x3f(x_102, x_1);
lean_dec(x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_inc(x_103);
x_19 = x_103;
x_20 = x_103;
goto block_99;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec(x_104);
x_19 = x_103;
x_20 = x_105;
goto block_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_108; 
x_11 = lean_box(0);
x_18 = lean_array_uget(x_2, x_4);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_101 = lean_ctor_get(x_6, 5);
x_102 = lean_ctor_get(x_18, 0);
lean_inc(x_102);
x_103 = l_Lean_replaceRef(x_102, x_101);
lean_dec(x_102);
x_108 = l_Lean_Syntax_getPos_x3f(x_103, x_1);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_unsigned_to_nat(0u);
x_104 = x_109;
goto block_107;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
lean_dec(x_108);
x_104 = x_110;
goto block_107;
}
block_17:
{
lean_object* x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_usize_add(x_4, x_12);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(x_1, x_2, x_3, x_15, x_14, x_6, x_8);
return x_16;
}
block_100:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; lean_object* x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_array_get_size(x_22);
x_26 = lean_uint64_of_nat(x_20);
x_27 = lean_uint64_of_nat(x_21);
x_28 = lean_uint64_mix_hash(x_26, x_27);
x_29 = lean_unsigned_to_nat(32u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_unsigned_to_nat(16u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_sub(x_38, x_40);
x_42 = lean_usize_land(x_37, x_41);
x_43 = lean_array_uget(x_22, x_42);
lean_dec(x_22);
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
x_46 = !lean_is_exclusive(x_19);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; uint8_t x_58; 
x_47 = lean_ctor_get(x_19, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_19, 0);
lean_dec(x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_20);
lean_ctor_set(x_49, 1, x_21);
x_50 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_49, x_24, x_43);
lean_dec(x_43);
lean_dec(x_24);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_dec(x_18);
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_array_get_size(x_45);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = lean_usize_sub(x_54, x_40);
x_56 = lean_usize_land(x_37, x_55);
x_57 = lean_array_uget(x_45, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_49, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_59 = lean_nat_add(x_44, x_39);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_57);
x_61 = lean_array_uset(x_45, x_56, x_60);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_shiftl(x_59, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_61);
lean_ctor_set(x_19, 1, x_68);
lean_ctor_set(x_19, 0, x_59);
x_12 = x_40;
x_13 = x_19;
goto block_17;
}
else
{
lean_ctor_set(x_19, 1, x_61);
lean_ctor_set(x_19, 0, x_59);
x_12 = x_40;
x_13 = x_19;
goto block_17;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_box(0);
x_70 = lean_array_uset(x_45, x_56, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_49, x_52, x_57);
x_72 = lean_array_uset(x_70, x_56, x_71);
lean_ctor_set(x_19, 1, x_72);
x_12 = x_40;
x_13 = x_19;
goto block_17;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; size_t x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_19);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_20);
lean_ctor_set(x_73, 1, x_21);
x_74 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_73, x_24, x_43);
lean_dec(x_43);
lean_dec(x_24);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_dec(x_18);
x_76 = lean_array_push(x_74, x_75);
x_77 = lean_array_get_size(x_45);
x_78 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_79 = lean_usize_sub(x_78, x_40);
x_80 = lean_usize_land(x_37, x_79);
x_81 = lean_array_uget(x_45, x_80);
x_82 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_73, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_nat_add(x_44, x_39);
lean_dec(x_44);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set(x_84, 2, x_81);
x_85 = lean_array_uset(x_45, x_80, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_nat_shiftl(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__4___redArg(x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_83);
lean_ctor_set(x_93, 1, x_92);
x_12 = x_40;
x_13 = x_93;
goto block_17;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_85);
x_12 = x_40;
x_13 = x_94;
goto block_17;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_box(0);
x_96 = lean_array_uset(x_45, x_80, x_95);
x_97 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__7___redArg(x_73, x_76, x_81);
x_98 = lean_array_uset(x_96, x_80, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_44);
lean_ctor_set(x_99, 1, x_98);
x_12 = x_40;
x_13 = x_99;
goto block_17;
}
}
}
block_107:
{
lean_object* x_105; 
x_105 = l_Lean_Syntax_getTailPos_x3f(x_103, x_1);
lean_dec(x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_inc(x_104);
x_20 = x_104;
x_21 = x_104;
goto block_100;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
x_20 = x_104;
x_21 = x_106;
goto block_100;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_3);
x_8 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_1, x_3, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_array_size(x_18);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12(x_1, x_18, x_21, x_23, x_20, x_4, x_5, x_16);
lean_dec(x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_25);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_19; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_19 = lean_string_dec_eq(x_6, x_3);
if (x_19 == 0)
{
x_7 = x_1;
goto block_18;
}
else
{
x_7 = x_2;
goto block_18;
}
block_18:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_mk_string_unchecked("Elab", 4, 4);
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_mk_string_unchecked("Tactic", 6, 6);
x_13 = lean_string_dec_eq(x_9, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
x_15 = lean_string_dec_eq(x_6, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
x_17 = lean_string_dec_eq(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
if (lean_obj_tag(x_8) == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
}
default: 
{
return x_1;
}
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_4, x_3);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_5);
x_18 = lean_array_uget(x_2, x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; double x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_97; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_box(0);
x_27 = lean_mk_string_unchecked("trace", 5, 5);
lean_inc(x_27);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_box(0);
x_30 = lean_float_of_nat(x_25);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_30);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_16);
x_33 = l_Lean_MessageData_nil;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_20);
lean_ctor_set_tag(x_19, 8);
lean_ctor_set(x_19, 1, x_34);
lean_ctor_set(x_19, 0, x_28);
x_35 = lean_ctor_get(x_6, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Elab_mkMessageCore(x_35, x_36, x_19, x_38, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_97 = lean_ctor_get_uint8(x_6, sizeof(void*)*13 + 1);
if (x_97 == 0)
{
lean_dec(x_27);
lean_inc(x_6);
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
goto block_96;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_box(x_1);
x_99 = lean_box(x_97);
x_100 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0___boxed), 4, 3);
lean_closure_set(x_100, 0, x_98);
lean_closure_set(x_100, 1, x_99);
lean_closure_set(x_100, 2, x_27);
x_101 = lean_ctor_get(x_39, 4);
lean_inc(x_101);
x_102 = l_Lean_MessageData_hasTag(x_100, x_101);
if (x_102 == 0)
{
lean_dec(x_39);
lean_dec(x_21);
x_9 = x_26;
x_10 = x_8;
goto block_15;
}
else
{
lean_inc(x_6);
x_40 = x_6;
x_41 = x_7;
x_42 = x_8;
goto block_96;
}
}
block_96:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_40, 6);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 7);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_st_ref_take(x_41, x_42);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 0, x_43);
x_49 = lean_ctor_get(x_39, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_39, 2);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_39, sizeof(void*)*5);
x_54 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 1);
x_55 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 2);
x_56 = lean_ctor_get(x_39, 3);
lean_inc(x_56);
lean_dec(x_39);
if (lean_is_scalar(x_21)) {
 x_57 = lean_alloc_ctor(4, 2, 0);
} else {
 x_57 = x_21;
 lean_ctor_set_tag(x_57, 4);
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_49);
x_58 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_56);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*5, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*5 + 1, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*5 + 2, x_55);
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_47, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_47, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 5);
lean_inc(x_64);
x_65 = l_Lean_MessageLog_add(x_58, x_64);
x_66 = lean_ctor_get(x_47, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_47, 7);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
lean_ctor_set(x_68, 2, x_61);
lean_ctor_set(x_68, 3, x_62);
lean_ctor_set(x_68, 4, x_63);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_41, x_68, x_48);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_9 = x_26;
x_10 = x_70;
goto block_15;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_71 = lean_ctor_get(x_45, 0);
x_72 = lean_ctor_get(x_45, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_45);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_43);
lean_ctor_set(x_73, 1, x_44);
x_74 = lean_ctor_get(x_39, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_39, sizeof(void*)*5);
x_79 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 1);
x_80 = lean_ctor_get_uint8(x_39, sizeof(void*)*5 + 2);
x_81 = lean_ctor_get(x_39, 3);
lean_inc(x_81);
lean_dec(x_39);
if (lean_is_scalar(x_21)) {
 x_82 = lean_alloc_ctor(4, 2, 0);
} else {
 x_82 = x_21;
 lean_ctor_set_tag(x_82, 4);
}
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_74);
x_83 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_76);
lean_ctor_set(x_83, 2, x_77);
lean_ctor_set(x_83, 3, x_81);
lean_ctor_set(x_83, 4, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_78);
lean_ctor_set_uint8(x_83, sizeof(void*)*5 + 1, x_79);
lean_ctor_set_uint8(x_83, sizeof(void*)*5 + 2, x_80);
x_84 = lean_ctor_get(x_71, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_71, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_71, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_71, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_71, 5);
lean_inc(x_89);
x_90 = l_Lean_MessageLog_add(x_83, x_89);
x_91 = lean_ctor_get(x_71, 6);
lean_inc(x_91);
x_92 = lean_ctor_get(x_71, 7);
lean_inc(x_92);
lean_dec(x_71);
x_93 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_86);
lean_ctor_set(x_93, 3, x_87);
lean_ctor_set(x_93, 4, x_88);
lean_ctor_set(x_93, 5, x_90);
lean_ctor_set(x_93, 6, x_91);
lean_ctor_set(x_93, 7, x_92);
x_94 = lean_st_ref_set(x_41, x_93, x_72);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_9 = x_26;
x_10 = x_95;
goto block_15;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; double x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_154; 
x_103 = lean_ctor_get(x_19, 0);
x_104 = lean_ctor_get(x_19, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_19);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_box(0);
x_107 = lean_mk_string_unchecked("trace", 5, 5);
lean_inc(x_107);
x_108 = l_Lean_Name_mkStr1(x_107);
x_109 = lean_box(0);
x_110 = lean_float_of_nat(x_105);
x_111 = lean_mk_string_unchecked("", 0, 0);
x_112 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_float(x_112, sizeof(void*)*2, x_110);
lean_ctor_set_float(x_112, sizeof(void*)*2 + 8, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*2 + 16, x_16);
x_113 = l_Lean_MessageData_nil;
x_114 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_20);
x_115 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_ctor_get(x_6, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_6, 1);
lean_inc(x_117);
x_118 = lean_box(0);
x_119 = lean_unbox(x_118);
x_120 = l_Lean_Elab_mkMessageCore(x_116, x_117, x_115, x_119, x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
x_154 = lean_ctor_get_uint8(x_6, sizeof(void*)*13 + 1);
if (x_154 == 0)
{
lean_dec(x_107);
lean_inc(x_6);
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
goto block_153;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_box(x_1);
x_156 = lean_box(x_154);
x_157 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0___boxed), 4, 3);
lean_closure_set(x_157, 0, x_155);
lean_closure_set(x_157, 1, x_156);
lean_closure_set(x_157, 2, x_107);
x_158 = lean_ctor_get(x_120, 4);
lean_inc(x_158);
x_159 = l_Lean_MessageData_hasTag(x_157, x_158);
if (x_159 == 0)
{
lean_dec(x_120);
lean_dec(x_21);
x_9 = x_106;
x_10 = x_8;
goto block_15;
}
else
{
lean_inc(x_6);
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
goto block_153;
}
}
block_153:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_124 = lean_ctor_get(x_121, 6);
lean_inc(x_124);
x_125 = lean_ctor_get(x_121, 7);
lean_inc(x_125);
lean_dec(x_121);
x_126 = lean_st_ref_take(x_122, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_ctor_get(x_120, 4);
lean_inc(x_131);
x_132 = lean_ctor_get(x_120, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_120, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_120, 2);
lean_inc(x_134);
x_135 = lean_ctor_get_uint8(x_120, sizeof(void*)*5);
x_136 = lean_ctor_get_uint8(x_120, sizeof(void*)*5 + 1);
x_137 = lean_ctor_get_uint8(x_120, sizeof(void*)*5 + 2);
x_138 = lean_ctor_get(x_120, 3);
lean_inc(x_138);
lean_dec(x_120);
if (lean_is_scalar(x_21)) {
 x_139 = lean_alloc_ctor(4, 2, 0);
} else {
 x_139 = x_21;
 lean_ctor_set_tag(x_139, 4);
}
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_131);
x_140 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_140, 0, x_132);
lean_ctor_set(x_140, 1, x_133);
lean_ctor_set(x_140, 2, x_134);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set(x_140, 4, x_139);
lean_ctor_set_uint8(x_140, sizeof(void*)*5, x_135);
lean_ctor_set_uint8(x_140, sizeof(void*)*5 + 1, x_136);
lean_ctor_set_uint8(x_140, sizeof(void*)*5 + 2, x_137);
x_141 = lean_ctor_get(x_127, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_127, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_127, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_127, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_127, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_127, 5);
lean_inc(x_146);
x_147 = l_Lean_MessageLog_add(x_140, x_146);
x_148 = lean_ctor_get(x_127, 6);
lean_inc(x_148);
x_149 = lean_ctor_get(x_127, 7);
lean_inc(x_149);
lean_dec(x_127);
x_150 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_142);
lean_ctor_set(x_150, 2, x_143);
lean_ctor_set(x_150, 3, x_144);
lean_ctor_set(x_150, 4, x_145);
lean_ctor_set(x_150, 5, x_147);
lean_ctor_set(x_150, 6, x_148);
lean_ctor_set(x_150, 7, x_149);
x_151 = lean_st_ref_set(x_122, x_150, x_128);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_9 = x_106;
x_10 = x_152;
goto block_15;
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_9;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_nat_dec_lt(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17(x_4, x_6);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = l_Lean_trace_profiler_output;
x_6 = l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(x_4, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_PersistentArray_isEmpty___redArg(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_41; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_free_object(x_7);
x_12 = lean_unsigned_to_nat(8u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_shiftl(x_12, x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
x_18 = l_Nat_nextPowerOfTwo(x_17);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_11, x_9, x_21, x_1, x_2, x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_48);
x_49 = lean_mk_empty_array_with_capacity(x_48);
lean_dec(x_48);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
lean_dec(x_23);
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_13, x_51);
if (x_52 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
x_41 = x_49;
goto block_47;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_51, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
x_41 = x_49;
goto block_47;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = lean_usize_of_nat(x_13);
x_55 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_56 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(x_50, x_54, x_55, x_49);
lean_dec(x_50);
x_41 = x_56;
goto block_47;
}
}
block_34:
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_box(0);
x_27 = lean_array_size(x_25);
x_28 = lean_usize_of_nat(x_13);
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(x_11, x_25, x_27, x_28, x_26, x_1, x_2, x_24);
lean_dec(x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_26);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
block_40:
{
lean_object* x_39; 
lean_dec(x_37);
x_39 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_35, x_38, x_36);
lean_dec(x_36);
x_25 = x_39;
goto block_34;
}
block_47:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_array_get_size(x_41);
x_43 = lean_nat_dec_eq(x_42, x_13);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_42, x_44);
x_46 = lean_nat_dec_le(x_13, x_45);
if (x_46 == 0)
{
lean_inc(x_45);
x_35 = x_41;
x_36 = x_45;
x_37 = x_42;
x_38 = x_45;
goto block_40;
}
else
{
x_35 = x_41;
x_36 = x_45;
x_37 = x_42;
x_38 = x_13;
goto block_40;
}
}
else
{
lean_dec(x_42);
x_25 = x_41;
goto block_34;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_9);
lean_dec(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_7, 0, x_57);
return x_7;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_7, 0);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_7);
x_60 = l_Lean_PersistentArray_isEmpty___redArg(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_89; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_61 = lean_unsigned_to_nat(8u);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_nat_shiftl(x_61, x_63);
x_65 = lean_unsigned_to_nat(3u);
x_66 = lean_nat_div(x_64, x_65);
lean_dec(x_64);
x_67 = l_Nat_nextPowerOfTwo(x_66);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = lean_mk_array(x_67, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_60, x_58, x_70, x_1, x_2, x_59);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_96 = lean_ctor_get(x_72, 0);
lean_inc(x_96);
x_97 = lean_mk_empty_array_with_capacity(x_96);
lean_dec(x_96);
x_98 = lean_ctor_get(x_72, 1);
lean_inc(x_98);
lean_dec(x_72);
x_99 = lean_array_get_size(x_98);
x_100 = lean_nat_dec_lt(x_62, x_99);
if (x_100 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
x_89 = x_97;
goto block_95;
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_99, x_99);
if (x_101 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
x_89 = x_97;
goto block_95;
}
else
{
size_t x_102; size_t x_103; lean_object* x_104; 
x_102 = lean_usize_of_nat(x_62);
x_103 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_104 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(x_98, x_102, x_103, x_97);
lean_dec(x_98);
x_89 = x_104;
goto block_95;
}
}
block_82:
{
lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_box(0);
x_76 = lean_array_size(x_74);
x_77 = lean_usize_of_nat(x_62);
x_78 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(x_60, x_74, x_76, x_77, x_75, x_1, x_2, x_73);
lean_dec(x_74);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
block_88:
{
lean_object* x_87; 
lean_dec(x_85);
x_87 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_83, x_86, x_84);
lean_dec(x_84);
x_74 = x_87;
goto block_82;
}
block_95:
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_array_get_size(x_89);
x_91 = lean_nat_dec_eq(x_90, x_62);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_sub(x_90, x_92);
x_94 = lean_nat_dec_le(x_62, x_93);
if (x_94 == 0)
{
lean_inc(x_93);
x_83 = x_89;
x_84 = x_93;
x_85 = x_90;
x_86 = x_93;
goto block_88;
}
else
{
x_83 = x_89;
x_84 = x_93;
x_85 = x_90;
x_86 = x_62;
goto block_88;
}
}
else
{
lean_dec(x_90);
x_74 = x_89;
goto block_82;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_58);
lean_dec(x_1);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_59);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_6);
lean_dec(x_1);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_3);
return x_108;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 12);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_checkTraceOption(x_4, x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_replaceRef(x_3, x_8);
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 4);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_24 = lean_ctor_get(x_5, 11);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_26 = lean_ctor_get(x_5, 12);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_27 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_15);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_17);
lean_ctor_set(x_27, 5, x_12);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_24);
lean_ctor_set(x_27, 12, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*13, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*13 + 1, x_25);
x_28 = lean_ctor_get(x_10, 3);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PersistentArray_toArray___redArg(x_29);
lean_dec(x_29);
x_31 = lean_array_size(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_usize_of_nat(x_32);
x_34 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(x_31, x_33, x_30);
x_35 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_4);
lean_ctor_set(x_35, 2, x_34);
x_36 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_35, x_27, x_6, x_11);
lean_dec(x_27);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_take(x_6, x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 3);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_46, sizeof(void*)*1);
lean_dec(x_46);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 0, x_3);
x_48 = l_Lean_PersistentArray_push___redArg(x_1, x_39);
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_47);
x_50 = lean_ctor_get(x_41, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 5);
lean_inc(x_51);
x_52 = lean_ctor_get(x_41, 6);
lean_inc(x_52);
x_53 = lean_ctor_get(x_41, 7);
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_49);
lean_ctor_set(x_54, 4, x_50);
lean_ctor_set(x_54, 5, x_51);
lean_ctor_set(x_54, 6, x_52);
lean_ctor_set(x_54, 7, x_53);
x_55 = lean_st_ref_set(x_6, x_54, x_42);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_box(0);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_62 = lean_ctor_get(x_39, 0);
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_39);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 3);
lean_inc(x_67);
x_68 = lean_ctor_get_uint64(x_67, sizeof(void*)*1);
lean_dec(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_37);
x_70 = l_Lean_PersistentArray_push___redArg(x_1, x_69);
x_71 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_uint64(x_71, sizeof(void*)*1, x_68);
x_72 = lean_ctor_get(x_62, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_62, 7);
lean_inc(x_75);
lean_dec(x_62);
x_76 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_76, 0, x_64);
lean_ctor_set(x_76, 1, x_65);
lean_ctor_set(x_76, 2, x_66);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_72);
lean_ctor_set(x_76, 5, x_73);
lean_ctor_set(x_76, 6, x_74);
lean_ctor_set(x_76, 7, x_75);
x_77 = lean_st_ref_set(x_6, x_76, x_63);
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
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
double x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; double x_30; lean_object* x_31; double x_32; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; double x_53; double x_54; lean_object* x_55; uint8_t x_56; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; double x_83; lean_object* x_84; double x_85; double x_86; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; double x_94; double x_95; lean_object* x_96; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_163; 
lean_inc(x_1);
x_45 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_1, x_6, x_8);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_90 = lean_ctor_get(x_6, 2);
lean_inc(x_90);
x_163 = lean_unbox(x_46);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = l_Lean_trace_profiler;
x_165 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_90, x_164);
if (x_165 == 0)
{
lean_object* x_166; 
lean_dec(x_90);
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_apply_3(x_3, x_6, x_7, x_47);
return x_166;
}
else
{
goto block_162;
}
}
else
{
goto block_162;
}
block_25:
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(0u);
if (x_13 == 0)
{
double x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_float_of_nat(x_17);
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_18);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_4);
x_20 = lean_box(0);
x_21 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(x_10, x_12, x_15, x_11, x_19, x_20, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set_float(x_22, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_22, sizeof(void*)*2 + 8, x_9);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 16, x_4);
x_23 = lean_box(0);
x_24 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(x_10, x_12, x_15, x_11, x_22, x_23, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_11);
return x_24;
}
}
block_44:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_6, 5);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
x_34 = lean_apply_4(x_2, x_28, x_6, x_7, x_31);
if (lean_obj_tag(x_34) == 0)
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_9 = x_32;
x_10 = x_26;
x_11 = x_27;
x_12 = x_33;
x_13 = x_29;
x_14 = x_30;
x_15 = x_35;
x_16 = x_36;
goto block_25;
}
else
{
uint8_t x_37; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_ctor_set_tag(x_34, 1);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_9 = x_32;
x_10 = x_26;
x_11 = x_27;
x_12 = x_33;
x_13 = x_29;
x_14 = x_30;
x_15 = x_43;
x_16 = x_41;
goto block_25;
}
}
block_77:
{
uint8_t x_57; 
x_57 = lean_unbox(x_46);
lean_dec(x_46);
if (x_57 == 0)
{
if (x_56 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_st_ref_take(x_7, x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 3);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_64, sizeof(void*)*1);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_PersistentArray_append___redArg(x_50, x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set_uint64(x_68, sizeof(void*)*1, x_65);
x_69 = lean_ctor_get(x_59, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_59, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 7);
lean_inc(x_72);
lean_dec(x_59);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_63);
lean_ctor_set(x_73, 3, x_68);
lean_ctor_set(x_73, 4, x_69);
lean_ctor_set(x_73, 5, x_70);
lean_ctor_set(x_73, 6, x_71);
lean_ctor_set(x_73, 7, x_72);
x_74 = lean_st_ref_set(x_7, x_73, x_60);
lean_dec(x_7);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_51, x_75);
lean_dec(x_51);
return x_76;
}
else
{
lean_dec(x_50);
x_26 = x_48;
x_27 = x_49;
x_28 = x_51;
x_29 = x_52;
x_30 = x_53;
x_31 = x_55;
x_32 = x_54;
goto block_44;
}
}
else
{
lean_dec(x_50);
x_26 = x_48;
x_27 = x_49;
x_28 = x_51;
x_29 = x_52;
x_30 = x_53;
x_31 = x_55;
x_32 = x_54;
goto block_44;
}
}
block_89:
{
double x_87; uint8_t x_88; 
x_87 = lean_float_sub(x_85, x_83);
x_88 = lean_float_decLt(x_86, x_87);
x_48 = x_78;
x_49 = x_79;
x_50 = x_80;
x_51 = x_81;
x_52 = x_82;
x_53 = x_83;
x_54 = x_85;
x_55 = x_84;
x_56 = x_88;
goto block_77;
}
block_110:
{
lean_object* x_97; uint8_t x_98; 
x_97 = l_Lean_trace_profiler;
x_98 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_90, x_97);
if (x_98 == 0)
{
lean_dec(x_90);
lean_inc(x_93);
x_48 = x_91;
x_49 = x_93;
x_50 = x_92;
x_51 = x_93;
x_52 = x_98;
x_53 = x_94;
x_54 = x_95;
x_55 = x_96;
x_56 = x_98;
goto block_77;
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = l_Lean_trace_profiler_useHeartbeats;
x_100 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_90, x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; double x_103; lean_object* x_104; double x_105; double x_106; 
x_101 = l_Lean_trace_profiler_threshold;
x_102 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_90, x_101);
lean_dec(x_90);
x_103 = lean_float_of_nat(x_102);
x_104 = lean_unsigned_to_nat(1000u);
x_105 = lean_float_of_nat(x_104);
x_106 = lean_float_div(x_103, x_105);
lean_inc(x_93);
x_78 = x_91;
x_79 = x_93;
x_80 = x_92;
x_81 = x_93;
x_82 = x_98;
x_83 = x_94;
x_84 = x_96;
x_85 = x_95;
x_86 = x_106;
goto block_89;
}
else
{
lean_object* x_107; lean_object* x_108; double x_109; 
x_107 = l_Lean_trace_profiler_threshold;
x_108 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_90, x_107);
lean_dec(x_90);
x_109 = lean_float_of_nat(x_108);
lean_inc(x_93);
x_78 = x_91;
x_79 = x_93;
x_80 = x_92;
x_81 = x_93;
x_82 = x_98;
x_83 = x_94;
x_84 = x_96;
x_85 = x_95;
x_86 = x_109;
goto block_89;
}
}
}
block_125:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; double x_119; lean_object* x_120; double x_121; double x_122; double x_123; double x_124; 
x_116 = lean_io_mono_nanos_now(x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_float_of_nat(x_111);
x_120 = lean_unsigned_to_nat(1000000000u);
x_121 = lean_float_of_nat(x_120);
x_122 = lean_float_div(x_119, x_121);
x_123 = lean_float_of_nat(x_117);
x_124 = lean_float_div(x_123, x_121);
x_91 = x_112;
x_92 = x_113;
x_93 = x_114;
x_94 = x_122;
x_95 = x_124;
x_96 = x_118;
goto block_110;
}
block_136:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; double x_134; double x_135; 
x_131 = lean_io_get_num_heartbeats(x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_float_of_nat(x_127);
x_135 = lean_float_of_nat(x_132);
x_91 = x_126;
x_92 = x_128;
x_93 = x_129;
x_94 = x_134;
x_95 = x_135;
x_96 = x_133;
goto block_110;
}
block_162:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_137 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_7, x_47);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_trace_profiler_useHeartbeats;
x_141 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_90, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_io_mono_nanos_now(x_139);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_7);
lean_inc(x_6);
x_145 = lean_apply_3(x_3, x_6, x_7, x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_146);
lean_inc(x_138);
x_111 = x_143;
x_112 = x_138;
x_113 = x_138;
x_114 = x_148;
x_115 = x_147;
goto block_125;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
lean_dec(x_145);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_149);
lean_inc(x_138);
x_111 = x_143;
x_112 = x_138;
x_113 = x_138;
x_114 = x_151;
x_115 = x_150;
goto block_125;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_io_get_num_heartbeats(x_139);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_7);
lean_inc(x_6);
x_155 = lean_apply_3(x_3, x_6, x_7, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_156);
lean_inc(x_138);
x_126 = x_138;
x_127 = x_153;
x_128 = x_138;
x_129 = x_158;
x_130 = x_157;
goto block_136;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_159);
lean_inc(x_138);
x_126 = x_138;
x_127 = x_153;
x_128 = x_138;
x_129 = x_161;
x_130 = x_160;
goto block_136;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_18; uint8_t x_19; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_18 = lean_mk_string_unchecked("trace", 5, 5);
x_19 = lean_string_dec_eq(x_5, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
x_6 = x_1;
goto block_17;
}
else
{
x_6 = x_2;
goto block_17;
}
block_17:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_mk_string_unchecked("Elab", 4, 4);
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_mk_string_unchecked("Tactic", 6, 6);
x_12 = lean_string_dec_eq(x_8, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
x_14 = lean_string_dec_eq(x_5, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
x_16 = lean_string_dec_eq(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
return x_1;
}
else
{
return x_1;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
}
default: 
{
return x_1;
}
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_125; uint8_t x_135; uint8_t x_136; 
x_118 = lean_box(2);
x_135 = lean_unbox(x_118);
x_136 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_135);
if (x_136 == 0)
{
x_125 = x_136;
goto block_134;
}
else
{
uint8_t x_137; 
lean_inc(x_2);
x_137 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_125 = x_137;
goto block_134;
}
block_63:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 7);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_st_ref_take(x_16, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 0, x_18);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_11);
x_25 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_14);
lean_ctor_set(x_25, 3, x_8);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_25, sizeof(void*)*5 + 2, x_4);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_22, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 5);
lean_inc(x_31);
x_32 = l_Lean_MessageLog_add(x_25, x_31);
x_33 = lean_ctor_get(x_22, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 7);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_29);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_33);
lean_ctor_set(x_35, 7, x_34);
x_36 = lean_st_ref_set(x_16, x_35, x_23);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_19);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_11);
x_47 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_12);
lean_ctor_set(x_47, 2, x_14);
lean_ctor_set(x_47, 3, x_8);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_47, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_47, sizeof(void*)*5 + 2, x_4);
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_43, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_43, 5);
lean_inc(x_53);
x_54 = l_Lean_MessageLog_add(x_47, x_53);
x_55 = lean_ctor_get(x_43, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_43, 7);
lean_inc(x_56);
lean_dec(x_43);
x_57 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_49);
lean_ctor_set(x_57, 2, x_50);
lean_ctor_set(x_57, 3, x_51);
lean_ctor_set(x_57, 4, x_52);
lean_ctor_set(x_57, 5, x_54);
lean_ctor_set(x_57, 6, x_55);
lean_ctor_set(x_57, 7, x_56);
x_58 = lean_st_ref_set(x_16, x_57, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
block_100:
{
lean_object* x_69; uint8_t x_70; 
x_69 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_2, x_5, x_6, x_7);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_ctor_get(x_5, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_5, 0);
lean_inc(x_74);
lean_inc(x_73);
x_75 = l_Lean_FileMap_toPosition(x_73, x_67);
lean_dec(x_67);
x_76 = l_Lean_FileMap_toPosition(x_73, x_68);
lean_dec(x_68);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_mk_string_unchecked("", 0, 0);
x_79 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
if (x_79 == 0)
{
lean_free_object(x_69);
x_8 = x_78;
x_9 = x_65;
x_10 = x_74;
x_11 = x_71;
x_12 = x_75;
x_13 = x_66;
x_14 = x_77;
x_15 = x_5;
x_16 = x_6;
x_17 = x_72;
goto block_63;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_box(x_64);
x_81 = lean_box(x_79);
x_82 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0___boxed), 3, 2);
lean_closure_set(x_82, 0, x_80);
lean_closure_set(x_82, 1, x_81);
lean_inc(x_71);
x_83 = l_Lean_MessageData_hasTag(x_82, x_71);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_5);
x_84 = lean_box(0);
lean_ctor_set(x_69, 0, x_84);
return x_69;
}
else
{
lean_free_object(x_69);
x_8 = x_78;
x_9 = x_65;
x_10 = x_74;
x_11 = x_71;
x_12 = x_75;
x_13 = x_66;
x_14 = x_77;
x_15 = x_5;
x_16 = x_6;
x_17 = x_72;
goto block_63;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_85 = lean_ctor_get(x_69, 0);
x_86 = lean_ctor_get(x_69, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_69);
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_5, 0);
lean_inc(x_88);
lean_inc(x_87);
x_89 = l_Lean_FileMap_toPosition(x_87, x_67);
lean_dec(x_67);
x_90 = l_Lean_FileMap_toPosition(x_87, x_68);
lean_dec(x_68);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_mk_string_unchecked("", 0, 0);
x_93 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
if (x_93 == 0)
{
x_8 = x_92;
x_9 = x_65;
x_10 = x_88;
x_11 = x_85;
x_12 = x_89;
x_13 = x_66;
x_14 = x_91;
x_15 = x_5;
x_16 = x_6;
x_17 = x_86;
goto block_63;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_box(x_64);
x_95 = lean_box(x_93);
x_96 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0___boxed), 3, 2);
lean_closure_set(x_96, 0, x_94);
lean_closure_set(x_96, 1, x_95);
lean_inc(x_85);
x_97 = l_Lean_MessageData_hasTag(x_96, x_85);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_5);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_86);
return x_99;
}
else
{
x_8 = x_92;
x_9 = x_65;
x_10 = x_88;
x_11 = x_85;
x_12 = x_89;
x_13 = x_66;
x_14 = x_91;
x_15 = x_5;
x_16 = x_6;
x_17 = x_86;
goto block_63;
}
}
}
}
block_108:
{
lean_object* x_106; 
x_106 = l_Lean_Syntax_getTailPos_x3f(x_104, x_102);
lean_dec(x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_inc(x_105);
x_64 = x_101;
x_65 = x_102;
x_66 = x_103;
x_67 = x_105;
x_68 = x_105;
goto block_100;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
x_64 = x_101;
x_65 = x_102;
x_66 = x_103;
x_67 = x_105;
x_68 = x_107;
goto block_100;
}
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_5, 5);
lean_inc(x_112);
x_113 = l_Lean_replaceRef(x_1, x_112);
lean_dec(x_112);
x_114 = l_Lean_Syntax_getPos_x3f(x_113, x_110);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_unsigned_to_nat(0u);
x_101 = x_109;
x_102 = x_110;
x_103 = x_111;
x_104 = x_113;
x_105 = x_115;
goto block_108;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_101 = x_109;
x_102 = x_110;
x_103 = x_111;
x_104 = x_113;
x_105 = x_116;
goto block_108;
}
}
block_124:
{
if (x_121 == 0)
{
if (x_120 == 0)
{
x_109 = x_119;
x_110 = x_120;
x_111 = x_3;
goto block_117;
}
else
{
uint8_t x_122; 
x_122 = lean_unbox(x_118);
x_109 = x_119;
x_110 = x_120;
x_111 = x_122;
goto block_117;
}
}
else
{
uint8_t x_123; 
x_123 = lean_unbox(x_118);
x_109 = x_119;
x_110 = x_120;
x_111 = x_123;
goto block_117;
}
}
block_134:
{
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_126 = lean_box(1);
x_127 = lean_unbox(x_126);
x_128 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_127);
if (x_128 == 0)
{
x_119 = x_125;
x_120 = x_125;
x_121 = x_128;
goto block_124;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_5, 2);
lean_inc(x_129);
x_130 = l_Lean_warningAsError;
x_131 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_129, x_130);
lean_dec(x_129);
x_119 = x_125;
x_120 = x_125;
x_121 = x_131;
goto block_124;
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_5);
lean_dec(x_2);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_7);
return x_133;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 5);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(x_6, x_1, x_2, x_8, x_3, x_4, x_5);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(x_1, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_get_set_stderr(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(x_7, x_9, x_21, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_get_set_stdout(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(x_7, x_9, x_21, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_get_set_stdin(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg___lam__0(x_7, x_9, x_13, x_12);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg___lam__0(x_7, x_9, x_21, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_1 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg(x_3, x_2, x_4, x_5, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = l_ByteArray_empty;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_14);
x_15 = lean_st_mk_ref(x_14, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_mk_ref(x_14, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_IO_FS_Stream_ofBuffer(x_16);
lean_inc(x_19);
x_22 = l_IO_FS_Stream_ofBuffer(x_19);
x_23 = lean_box(x_2);
lean_inc(x_22);
x_24 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_22);
x_25 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29), 6, 3);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, x_22);
lean_closure_set(x_25, 2, x_24);
x_26 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg(x_21, x_25, x_3, x_4, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_19, x_28);
lean_dec(x_19);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_string_validate_utf8(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_32);
x_34 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
x_35 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
x_36 = lean_unsigned_to_nat(128u);
x_37 = lean_unsigned_to_nat(47u);
x_38 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_40 = l_panic___at___Lean_Name_getString_x21_spec__0(x_39);
x_6 = x_31;
x_7 = x_27;
x_8 = x_40;
goto block_11;
}
else
{
lean_object* x_41; 
x_41 = lean_string_from_utf8_unchecked(x_32);
lean_dec(x_32);
x_6 = x_31;
x_7 = x_27;
x_8 = x_41;
goto block_11;
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_16; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_26 = lean_io_get_tid(x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_take(x_5, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 2);
lean_inc(x_34);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_unsigned_to_nat(5u);
x_37 = lean_usize_of_nat(x_36);
x_38 = lean_usize_to_nat(x_37);
x_39 = lean_nat_pow(x_35, x_38);
lean_dec(x_38);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = lean_usize_to_nat(x_40);
x_42 = lean_mk_empty_array_with_capacity(x_41);
lean_dec(x_41);
lean_inc(x_42);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_unsigned_to_nat(0u);
lean_inc(x_42);
x_45 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set_usize(x_45, 4, x_37);
x_46 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_unbox_uint64(x_27);
lean_dec(x_27);
lean_ctor_set_uint64(x_46, sizeof(void*)*1, x_47);
x_48 = lean_ctor_get(x_30, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_30, 5);
lean_inc(x_49);
lean_dec(x_30);
x_50 = l_Lean_MessageLog_markAllReported(x_49);
x_51 = lean_box(1);
x_52 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_52);
lean_inc(x_42);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_42);
x_56 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_42);
lean_ctor_set(x_56, 2, x_44);
lean_ctor_set(x_56, 3, x_44);
lean_ctor_set_usize(x_56, 4, x_37);
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_unbox(x_51);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_58);
x_59 = lean_mk_empty_array_with_capacity(x_44);
x_60 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_60, 0, x_32);
lean_ctor_set(x_60, 1, x_33);
lean_ctor_set(x_60, 2, x_34);
lean_ctor_set(x_60, 3, x_46);
lean_ctor_set(x_60, 4, x_48);
lean_ctor_set(x_60, 5, x_50);
lean_ctor_set(x_60, 6, x_57);
lean_ctor_set(x_60, 7, x_59);
x_61 = lean_st_ref_set(x_5, x_60, x_31);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_mk_string_unchecked("Elab", 4, 4);
x_64 = lean_mk_string_unchecked("async", 5, 5);
x_65 = l_Lean_Name_mkStr2(x_63, x_64);
x_66 = lean_apply_1(x_1, x_2);
x_67 = lean_mk_string_unchecked("", 0, 0);
x_68 = lean_unbox(x_51);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_65, x_3, x_66, x_68, x_67, x_4, x_5, x_62);
if (lean_obj_tag(x_69) == 0)
{
x_16 = x_69;
goto block_25;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Exception_isInterrupt(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_Exception_toMessageData(x_70);
lean_inc(x_4);
x_74 = l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(x_73, x_4, x_5, x_71);
x_16 = x_74;
goto block_25;
}
else
{
lean_dec(x_70);
x_7 = x_71;
goto block_15;
}
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(x_4, x_5, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_5, x_9);
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
block_25:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_7 = x_17;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(x_4, x_5, x_19);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__1), 6, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = l_Lean_Core_stderrAsMessages;
x_10 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_8, x_9);
lean_dec(x_8);
x_11 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(x_7, x_10, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Core_mkSnapshot(x_9, x_2, x_10, x_3, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = l_Array_empty(lean_box(0));
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
lean_inc(x_15);
x_20 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set_usize(x_20, 4, x_19);
x_21 = lean_box(0);
lean_inc(x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_uint64_of_nat(x_18);
lean_inc(x_15);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_15);
lean_inc(x_15);
x_28 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_17);
lean_ctor_set(x_28, 3, x_17);
lean_ctor_set_usize(x_28, 4, x_19);
x_29 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint64(x_29, sizeof(void*)*1, x_26);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_15);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_33);
return x_6;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
lean_dec(x_6);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = l_Array_empty(lean_box(0));
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_usize_of_nat(x_39);
lean_inc(x_36);
x_41 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set_usize(x_41, 4, x_40);
x_42 = lean_box(0);
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(0);
x_47 = lean_uint64_of_nat(x_39);
lean_inc(x_36);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_36);
lean_inc(x_36);
x_49 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_38);
lean_ctor_set_usize(x_49, 4, x_40);
x_50 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint64(x_50, sizeof(void*)*1, x_47);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_52, 0, x_35);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_36);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_34);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed), 5, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__2), 6, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
lean_inc(x_4);
x_9 = l_Lean_Core_wrapAsync___redArg(x_8, x_2, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3), 5, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_3);
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
x_15 = lean_alloc_closure((void*)(l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__3), 5, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__8(x_10, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___redArg(x_8, x_2, x_9, x_10, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9_spec__9(x_9, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8_spec__9(x_9, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__8(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___redArg(x_8, x_2, x_9, x_10, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12_spec__12(x_9, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8_spec__12(x_9, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentArray_forIn___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__8(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___lam__0(x_5, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__15(x_9, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__16(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__17(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__18(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__20(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__23(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__28___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__29___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28_spec__30___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___redArg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_IO_FS_withIsolatedStreams___at___Lean_Core_wrapAsyncAsSnapshot_spec__28(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_wrapAsyncAsSnapshot___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_wrapAsyncAsSnapshot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Core_wrapAsyncAsSnapshot(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_25; uint8_t x_26; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_25 = lean_ctor_get(x_4, 4);
lean_inc(x_25);
x_26 = lean_nat_dec_le(x_1, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
x_11 = x_1;
goto block_24;
}
else
{
lean_dec(x_1);
x_11 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 10);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_19 = lean_ctor_get(x_4, 11);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_21 = lean_ctor_get(x_4, 12);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_8);
lean_ctor_set(x_22, 2, x_9);
lean_ctor_set(x_22, 3, x_10);
lean_ctor_set(x_22, 4, x_11);
lean_ctor_set(x_22, 5, x_12);
lean_ctor_set(x_22, 6, x_13);
lean_ctor_set(x_22, 7, x_14);
lean_ctor_set(x_22, 8, x_15);
lean_ctor_set(x_22, 9, x_16);
lean_ctor_set(x_22, 10, x_17);
lean_ctor_set(x_22, 11, x_19);
lean_ctor_set(x_22, 12, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*13, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*13 + 1, x_20);
x_23 = lean_apply_3(x_3, x_22, x_5, x_6);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_withAtLeastMaxRecDepth___redArg___lam__0), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_3(x_1, lean_box(0), x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withAtLeastMaxRecDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_withAtLeastMaxRecDepth___redArg___lam__0), 6, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_3(x_3, lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_9, lean_box(0), x_4);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_catchInternalId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_3(x_6, lean_box(0), x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_catchInternalId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_3(x_9, lean_box(0), x_6, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_catchInternalId___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_catchInternalId(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_6, lean_box(0), x_5);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = l_List_elem___redArg(x_2, x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_10, lean_box(0), x_5);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_apply_1(x_4, x_5);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_instBEqInternalExceptionId;
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___redArg___lam__0), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_7, lean_box(0), x_3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_instBEqInternalExceptionId;
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___redArg___lam__0), 5, 4);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_7);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_apply_3(x_10, lean_box(0), x_6, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_catchInternalIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_catchInternalIds(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxHeartbeat(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_box(0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_mk_string_unchecked("runtime", 7, 7);
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_11; 
x_11 = lean_unbox(x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_unbox(x_4);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_mk_string_unchecked("maxHeartbeats", 13, 13);
x_14 = lean_string_dec_eq(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_15; 
x_15 = lean_unbox(x_4);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_unbox(x_4);
return x_16;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
return x_14;
}
else
{
uint8_t x_17; 
x_17 = lean_unbox(x_4);
return x_17;
}
}
}
}
else
{
uint8_t x_18; 
x_18 = lean_unbox(x_4);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = lean_unbox(x_4);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxHeartbeat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isMaxHeartbeat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_mk_string_unchecked("x", 1, 1);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_6, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Expr_forallE___override(x_9, x_1, x_2, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Expr_forallE___override(x_13, x_1, x_2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrow___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkArrow___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrow(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_sub(x_2, x_9);
x_11 = lean_array_uget(x_1, x_10);
x_12 = l_Lean_mkArrow___redArg(x_11, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_2 = x_10;
x_4 = x_13;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrowN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = lean_usize_of_nat(x_7);
x_12 = l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(x_1, x_10, x_11, x_2, x_4, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldrMUnsafe_fold___at___Lean_mkArrowN_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkArrowN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkArrowN(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_CoreM_0__Lean_supportedRecursors() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Empty", 5, 5);
x_2 = lean_mk_string_unchecked("rec", 3, 3);
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_mk_string_unchecked("False", 5, 5);
lean_inc(x_2);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr2(x_4, x_2);
x_6 = lean_mk_string_unchecked("Eq", 2, 2);
x_7 = lean_mk_string_unchecked("ndrec", 5, 5);
lean_inc(x_6);
x_8 = l_Lean_Name_mkStr2(x_6, x_7);
lean_inc(x_2);
lean_inc(x_6);
x_9 = l_Lean_Name_mkStr2(x_6, x_2);
x_10 = lean_mk_string_unchecked("recOn", 5, 5);
lean_inc(x_6);
x_11 = l_Lean_Name_mkStr2(x_6, x_10);
x_12 = lean_mk_string_unchecked("casesOn", 7, 7);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr2(x_6, x_12);
lean_inc(x_12);
x_14 = l_Lean_Name_mkStr2(x_4, x_12);
lean_inc(x_12);
x_15 = l_Lean_Name_mkStr2(x_1, x_12);
x_16 = lean_mk_string_unchecked("And", 3, 3);
lean_inc(x_16);
x_17 = l_Lean_Name_mkStr2(x_16, x_2);
x_18 = l_Lean_Name_mkStr2(x_16, x_12);
x_19 = lean_unsigned_to_nat(10u);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_21 = lean_array_push(x_20, x_3);
x_22 = lean_array_push(x_21, x_5);
x_23 = lean_array_push(x_22, x_8);
x_24 = lean_array_push(x_23, x_9);
x_25 = lean_array_push(x_24, x_11);
x_26 = lean_array_push(x_25, x_13);
x_27 = lean_array_push(x_26, x_14);
x_28 = lean_array_push(x_27, x_15);
x_29 = lean_array_push(x_28, x_17);
x_30 = lean_array_push(x_29, x_18);
return x_30;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_14; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_is_aux_recursor(x_2, x_4);
if (x_16 == 0)
{
x_14 = x_16;
goto block_15;
}
else
{
uint8_t x_17; 
lean_inc(x_4);
lean_inc(x_2);
x_17 = l_Lean_isCasesOnRecursor(x_2, x_4);
if (x_17 == 0)
{
x_14 = x_16;
goto block_15;
}
else
{
goto block_13;
}
}
block_11:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_6 = l_Array_contains___redArg(x_1, x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
block_13:
{
uint8_t x_12; 
lean_inc(x_4);
x_12 = l_Lean_isRecCore(x_2, x_4);
if (x_12 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
else
{
goto block_11;
}
}
block_15:
{
if (x_14 == 0)
{
goto block_13;
}
else
{
lean_dec(x_2);
goto block_11;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_find_expr(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Expr_bvar___override(x_11);
lean_ctor_set(x_7, 0, x_12);
x_13 = lean_apply_1(x_2, x_7);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Expr_fvar___override(x_14);
lean_ctor_set(x_7, 0, x_15);
x_16 = lean_apply_1(x_2, x_7);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_Expr_mvar___override(x_17);
lean_ctor_set(x_7, 0, x_18);
x_19 = lean_apply_1(x_2, x_7);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l_Lean_Expr_sort___override(x_20);
lean_ctor_set(x_7, 0, x_21);
x_22 = lean_apply_1(x_2, x_7);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_7);
lean_dec(x_2);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = l_Lean_MessageData_ofName(x_23);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___redArg(x_3, x_4, x_30);
return x_31;
}
case 5:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = l_Lean_Expr_app___override(x_32, x_33);
lean_ctor_set(x_7, 0, x_34);
x_35 = lean_apply_1(x_2, x_7);
return x_35;
}
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_ctor_get(x_10, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_10, 2);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 8);
lean_dec(x_10);
x_40 = l_Lean_Expr_lam___override(x_36, x_37, x_38, x_39);
lean_ctor_set(x_7, 0, x_40);
x_41 = lean_apply_1(x_2, x_7);
return x_41;
}
case 7:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_10, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 8);
lean_dec(x_10);
x_46 = l_Lean_Expr_forallE___override(x_42, x_43, x_44, x_45);
lean_ctor_set(x_7, 0, x_46);
x_47 = lean_apply_1(x_2, x_7);
return x_47;
}
case 8:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_ctor_get(x_10, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_10, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_10, 3);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_10, sizeof(void*)*4 + 8);
lean_dec(x_10);
x_53 = l_Lean_Expr_letE___override(x_48, x_49, x_50, x_51, x_52);
lean_ctor_set(x_7, 0, x_53);
x_54 = lean_apply_1(x_2, x_7);
return x_54;
}
case 9:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_ctor_get(x_10, 0);
lean_inc(x_55);
lean_dec(x_10);
x_56 = l_Lean_Expr_lit___override(x_55);
lean_ctor_set(x_7, 0, x_56);
x_57 = lean_apply_1(x_2, x_7);
return x_57;
}
case 10:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_ctor_get(x_10, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_dec(x_10);
x_60 = l_Lean_Expr_mdata___override(x_58, x_59);
lean_ctor_set(x_7, 0, x_60);
x_61 = lean_apply_1(x_2, x_7);
return x_61;
}
default: 
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_4);
lean_dec(x_3);
x_62 = lean_ctor_get(x_10, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_10, 2);
lean_inc(x_64);
lean_dec(x_10);
x_65 = l_Lean_Expr_proj___override(x_62, x_63, x_64);
lean_ctor_set(x_7, 0, x_65);
x_66 = lean_apply_1(x_2, x_7);
return x_66;
}
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
lean_dec(x_7);
switch (lean_obj_tag(x_67)) {
case 0:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Expr_bvar___override(x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_apply_1(x_2, x_70);
return x_71;
}
case 1:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = l_Lean_Expr_fvar___override(x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_apply_1(x_2, x_74);
return x_75;
}
case 2:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_4);
lean_dec(x_3);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
lean_dec(x_67);
x_77 = l_Lean_Expr_mvar___override(x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_apply_1(x_2, x_78);
return x_79;
}
case 3:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_ctor_get(x_67, 0);
lean_inc(x_80);
lean_dec(x_67);
x_81 = l_Lean_Expr_sort___override(x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_apply_1(x_2, x_82);
return x_83;
}
case 4:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
x_84 = lean_ctor_get(x_67, 0);
lean_inc(x_84);
lean_dec(x_67);
x_85 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = l_Lean_MessageData_ofName(x_84);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_throwError___redArg(x_3, x_4, x_91);
return x_92;
}
case 5:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_4);
lean_dec(x_3);
x_93 = lean_ctor_get(x_67, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_67, 1);
lean_inc(x_94);
lean_dec(x_67);
x_95 = l_Lean_Expr_app___override(x_93, x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_apply_1(x_2, x_96);
return x_97;
}
case 6:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_ctor_get(x_67, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_67, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_67, 2);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_67, sizeof(void*)*3 + 8);
lean_dec(x_67);
x_102 = l_Lean_Expr_lam___override(x_98, x_99, x_100, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_apply_1(x_2, x_103);
return x_104;
}
case 7:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_ctor_get(x_67, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_67, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_67, 2);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_67, sizeof(void*)*3 + 8);
lean_dec(x_67);
x_109 = l_Lean_Expr_forallE___override(x_105, x_106, x_107, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_apply_1(x_2, x_110);
return x_111;
}
case 8:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_67, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_67, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_67, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_67, 3);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_67, sizeof(void*)*4 + 8);
lean_dec(x_67);
x_117 = l_Lean_Expr_letE___override(x_112, x_113, x_114, x_115, x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_apply_1(x_2, x_118);
return x_119;
}
case 9:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_ctor_get(x_67, 0);
lean_inc(x_120);
lean_dec(x_67);
x_121 = l_Lean_Expr_lit___override(x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_apply_1(x_2, x_122);
return x_123;
}
case 10:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_ctor_get(x_67, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_67, 1);
lean_inc(x_125);
lean_dec(x_67);
x_126 = l_Lean_Expr_mdata___override(x_124, x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_apply_1(x_2, x_127);
return x_128;
}
default: 
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_4);
lean_dec(x_3);
x_129 = lean_ctor_get(x_67, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_67, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_67, 2);
lean_inc(x_131);
lean_dec(x_67);
x_132 = l_Lean_Expr_proj___override(x_129, x_130, x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_apply_1(x_2, x_133);
return x_134;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2___boxed), 6, 4);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_box(0);
x_10 = l_Lean_Declaration_foldExprM___redArg(x_3, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_Name_instBEq;
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__3), 6, 5);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_CoreM_0__Lean_checkUnsupported___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_5018_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_mk_string_unchecked("compiler", 8, 8);
x_3 = lean_mk_string_unchecked("enableNew", 9, 9);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_mk_string_unchecked("(compiler) enable the new code generator, this should have no significant effect on your code but it does help to test the new code generator; unset to only use the old code generator instead", 191, 191);
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
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_2(x_3, x_5, x_6);
x_9 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_8, x_4, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_io_wait(x_1, x_4);
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
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_mk_string_unchecked("blocked", 7, 7);
x_7 = lean_box(0);
x_8 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_6, x_5, x_1, x_7, x_2, x_3, x_4);
lean_dec(x_5);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_io_get_task_state(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_task_get_own(x_2);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_task_get_own(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_15, 0, x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__1___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_traceBlock___redArg___lam__2), 4, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_mk_string_unchecked("Elab", 4, 4);
x_19 = lean_mk_string_unchecked("block", 5, 5);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_20, x_16, x_17, x_22, x_1, x_3, x_4, x_14);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_traceBlock___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_profileitM___at___Lean_traceBlock_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_traceBlock___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_traceBlock___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_traceBlock___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDeclsNew___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_lcnf_compile_decls(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDeclsOld___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_compile_decls(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_MessageData_ofName(x_5);
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
x_11 = l_Lean_MessageData_ofName(x_9);
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
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_13; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_15 = lean_is_aux_recursor(x_1, x_3);
if (x_15 == 0)
{
x_13 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_isCasesOnRecursor(x_1, x_3);
if (x_16 == 0)
{
x_13 = x_15;
goto block_14;
}
else
{
goto block_12;
}
}
block_10:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_5 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
block_12:
{
uint8_t x_11; 
lean_inc(x_3);
x_11 = l_Lean_isRecCore(x_1, x_3);
if (x_11 == 0)
{
lean_dec(x_3);
return x_11;
}
else
{
goto block_10;
}
}
block_14:
{
if (x_13 == 0)
{
goto block_12;
}
else
{
lean_dec(x_1);
goto block_10;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_find_expr(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Expr_bvar___override(x_12);
lean_ctor_set(x_8, 0, x_13);
x_14 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Expr_fvar___override(x_15);
lean_ctor_set(x_8, 0, x_16);
x_17 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = l_Lean_Expr_mvar___override(x_18);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_Expr_sort___override(x_21);
lean_ctor_set(x_8, 0, x_22);
x_23 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_8);
lean_dec(x_2);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_MessageData_ofName(x_24);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_31, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_32;
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_dec(x_11);
x_35 = l_Lean_Expr_app___override(x_33, x_34);
lean_ctor_set(x_8, 0, x_35);
x_36 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_36;
}
case 6:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 2);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_41 = l_Lean_Expr_lam___override(x_37, x_38, x_39, x_40);
lean_ctor_set(x_8, 0, x_41);
x_42 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_42;
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_11, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_47 = l_Lean_Expr_forallE___override(x_43, x_44, x_45, x_46);
lean_ctor_set(x_8, 0, x_47);
x_48 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_48;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_11, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_11, 3);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_11, sizeof(void*)*4 + 8);
lean_dec(x_11);
x_54 = l_Lean_Expr_letE___override(x_49, x_50, x_51, x_52, x_53);
lean_ctor_set(x_8, 0, x_54);
x_55 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_55;
}
case 9:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
lean_dec(x_11);
x_57 = l_Lean_Expr_lit___override(x_56);
lean_ctor_set(x_8, 0, x_57);
x_58 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_58;
}
case 10:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_dec(x_11);
x_61 = l_Lean_Expr_mdata___override(x_59, x_60);
lean_ctor_set(x_8, 0, x_61);
x_62 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_62;
}
default: 
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_11, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_11, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_11, 2);
lean_inc(x_65);
lean_dec(x_11);
x_66 = l_Lean_Expr_proj___override(x_63, x_64, x_65);
lean_ctor_set(x_8, 0, x_66);
x_67 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_67;
}
}
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_8, 0);
lean_inc(x_68);
lean_dec(x_8);
switch (lean_obj_tag(x_68)) {
case 0:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Expr_bvar___override(x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_apply_4(x_2, x_71, x_5, x_6, x_7);
return x_72;
}
case 1:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
x_74 = l_Lean_Expr_fvar___override(x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_apply_4(x_2, x_75, x_5, x_6, x_7);
return x_76;
}
case 2:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_68, 0);
lean_inc(x_77);
lean_dec(x_68);
x_78 = l_Lean_Expr_mvar___override(x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_apply_4(x_2, x_79, x_5, x_6, x_7);
return x_80;
}
case 3:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
lean_dec(x_68);
x_82 = l_Lean_Expr_sort___override(x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_apply_4(x_2, x_83, x_5, x_6, x_7);
return x_84;
}
case 4:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
x_85 = lean_ctor_get(x_68, 0);
lean_inc(x_85);
lean_dec(x_68);
x_86 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
x_88 = l_Lean_MessageData_ofName(x_85);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_92, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_93;
}
case 5:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_68, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_68, 1);
lean_inc(x_95);
lean_dec(x_68);
x_96 = l_Lean_Expr_app___override(x_94, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_apply_4(x_2, x_97, x_5, x_6, x_7);
return x_98;
}
case 6:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_68, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_68, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_68, 2);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_68, sizeof(void*)*3 + 8);
lean_dec(x_68);
x_103 = l_Lean_Expr_lam___override(x_99, x_100, x_101, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_apply_4(x_2, x_104, x_5, x_6, x_7);
return x_105;
}
case 7:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_68, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_68, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_68, 2);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_68, sizeof(void*)*3 + 8);
lean_dec(x_68);
x_110 = l_Lean_Expr_forallE___override(x_106, x_107, x_108, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_apply_4(x_2, x_111, x_5, x_6, x_7);
return x_112;
}
case 8:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_68, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_68, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_68, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_68, 3);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_68, sizeof(void*)*4 + 8);
lean_dec(x_68);
x_118 = l_Lean_Expr_letE___override(x_113, x_114, x_115, x_116, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_apply_4(x_2, x_119, x_5, x_6, x_7);
return x_120;
}
case 9:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_68, 0);
lean_inc(x_121);
lean_dec(x_68);
x_122 = l_Lean_Expr_lit___override(x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_apply_4(x_2, x_123, x_5, x_6, x_7);
return x_124;
}
case 10:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_68, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_68, 1);
lean_inc(x_126);
lean_dec(x_68);
x_127 = l_Lean_Expr_mdata___override(x_125, x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_apply_4(x_2, x_128, x_5, x_6, x_7);
return x_129;
}
default: 
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_68, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_68, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_68, 2);
lean_inc(x_132);
lean_dec(x_68);
x_133 = l_Lean_Expr_proj___override(x_130, x_131, x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_apply_4(x_2, x_134, x_5, x_6, x_7);
return x_135;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_15 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0___boxed), 4, 0);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_19 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__2(x_16, x_15, x_2, x_18, x_4, x_5, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__2(x_16, x_15, x_20, x_22, x_4, x_5, x_21);
lean_dec(x_20);
lean_dec(x_16);
x_10 = x_23;
goto block_14;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
x_10 = x_19;
goto block_14;
}
block_14:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_2 = x_11;
x_3 = x_9;
x_6 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_find_expr(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_3);
x_19 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
x_11 = x_19;
goto block_15;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_bvar___override(x_22);
lean_ctor_set(x_18, 0, x_23);
x_24 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_24;
goto block_15;
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_3);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_Expr_fvar___override(x_25);
lean_ctor_set(x_18, 0, x_26);
x_27 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_27;
goto block_15;
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_3);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Lean_Expr_mvar___override(x_28);
lean_ctor_set(x_18, 0, x_29);
x_30 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_30;
goto block_15;
}
case 3:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_3);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = l_Lean_Expr_sort___override(x_31);
lean_ctor_set(x_18, 0, x_32);
x_33 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_33;
goto block_15;
}
case 4:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_18);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = l_Lean_MessageData_ofName(x_34);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_3, 0, x_36);
x_38 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_40, x_4, x_5, x_6);
x_11 = x_41;
goto block_15;
}
case 5:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_3);
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_dec(x_21);
x_44 = l_Lean_Expr_app___override(x_42, x_43);
lean_ctor_set(x_18, 0, x_44);
x_45 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_45;
goto block_15;
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_3);
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_21, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 8);
lean_dec(x_21);
x_50 = l_Lean_Expr_lam___override(x_46, x_47, x_48, x_49);
lean_ctor_set(x_18, 0, x_50);
x_51 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_51;
goto block_15;
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_3);
x_52 = lean_ctor_get(x_21, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 8);
lean_dec(x_21);
x_56 = l_Lean_Expr_forallE___override(x_52, x_53, x_54, x_55);
lean_ctor_set(x_18, 0, x_56);
x_57 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_57;
goto block_15;
}
case 8:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_3);
x_58 = lean_ctor_get(x_21, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_21, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_21, 3);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 8);
lean_dec(x_21);
x_63 = l_Lean_Expr_letE___override(x_58, x_59, x_60, x_61, x_62);
lean_ctor_set(x_18, 0, x_63);
x_64 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_64;
goto block_15;
}
case 9:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_3);
x_65 = lean_ctor_get(x_21, 0);
lean_inc(x_65);
lean_dec(x_21);
x_66 = l_Lean_Expr_lit___override(x_65);
lean_ctor_set(x_18, 0, x_66);
x_67 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_67;
goto block_15;
}
case 10:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_3);
x_68 = lean_ctor_get(x_21, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
lean_dec(x_21);
x_70 = l_Lean_Expr_mdata___override(x_68, x_69);
lean_ctor_set(x_18, 0, x_70);
x_71 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_71;
goto block_15;
}
default: 
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_3);
x_72 = lean_ctor_get(x_21, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_21, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_21, 2);
lean_inc(x_74);
lean_dec(x_21);
x_75 = l_Lean_Expr_proj___override(x_72, x_73, x_74);
lean_ctor_set(x_18, 0, x_75);
x_76 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_76;
goto block_15;
}
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_18, 0);
lean_inc(x_77);
lean_dec(x_18);
switch (lean_obj_tag(x_77)) {
case 0:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_3);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Expr_bvar___override(x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_80, x_4, x_5, x_6);
lean_dec(x_80);
x_11 = x_81;
goto block_15;
}
case 1:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_free_object(x_3);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
lean_dec(x_77);
x_83 = l_Lean_Expr_fvar___override(x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_84, x_4, x_5, x_6);
lean_dec(x_84);
x_11 = x_85;
goto block_15;
}
case 2:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_3);
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
lean_dec(x_77);
x_87 = l_Lean_Expr_mvar___override(x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_88, x_4, x_5, x_6);
lean_dec(x_88);
x_11 = x_89;
goto block_15;
}
case 3:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_3);
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
lean_dec(x_77);
x_91 = l_Lean_Expr_sort___override(x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_92, x_4, x_5, x_6);
lean_dec(x_92);
x_11 = x_93;
goto block_15;
}
case 4:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_77, 0);
lean_inc(x_94);
lean_dec(x_77);
x_95 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = l_Lean_MessageData_ofName(x_94);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_97);
lean_ctor_set(x_3, 0, x_96);
x_98 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_3);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_100, x_4, x_5, x_6);
x_11 = x_101;
goto block_15;
}
case 5:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_3);
x_102 = lean_ctor_get(x_77, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_77, 1);
lean_inc(x_103);
lean_dec(x_77);
x_104 = l_Lean_Expr_app___override(x_102, x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_105, x_4, x_5, x_6);
lean_dec(x_105);
x_11 = x_106;
goto block_15;
}
case 6:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_3);
x_107 = lean_ctor_get(x_77, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_77, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_77, 2);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_77, sizeof(void*)*3 + 8);
lean_dec(x_77);
x_111 = l_Lean_Expr_lam___override(x_107, x_108, x_109, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_112, x_4, x_5, x_6);
lean_dec(x_112);
x_11 = x_113;
goto block_15;
}
case 7:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_free_object(x_3);
x_114 = lean_ctor_get(x_77, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_77, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_77, 2);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_77, sizeof(void*)*3 + 8);
lean_dec(x_77);
x_118 = l_Lean_Expr_forallE___override(x_114, x_115, x_116, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_119, x_4, x_5, x_6);
lean_dec(x_119);
x_11 = x_120;
goto block_15;
}
case 8:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_free_object(x_3);
x_121 = lean_ctor_get(x_77, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_77, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_77, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_77, 3);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_77, sizeof(void*)*4 + 8);
lean_dec(x_77);
x_126 = l_Lean_Expr_letE___override(x_121, x_122, x_123, x_124, x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_127, x_4, x_5, x_6);
lean_dec(x_127);
x_11 = x_128;
goto block_15;
}
case 9:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_3);
x_129 = lean_ctor_get(x_77, 0);
lean_inc(x_129);
lean_dec(x_77);
x_130 = l_Lean_Expr_lit___override(x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_131, x_4, x_5, x_6);
lean_dec(x_131);
x_11 = x_132;
goto block_15;
}
case 10:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_free_object(x_3);
x_133 = lean_ctor_get(x_77, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_77, 1);
lean_inc(x_134);
lean_dec(x_77);
x_135 = l_Lean_Expr_mdata___override(x_133, x_134);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_136, x_4, x_5, x_6);
lean_dec(x_136);
x_11 = x_137;
goto block_15;
}
default: 
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_free_object(x_3);
x_138 = lean_ctor_get(x_77, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_77, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_77, 2);
lean_inc(x_140);
lean_dec(x_77);
x_141 = l_Lean_Expr_proj___override(x_138, x_139, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_142, x_4, x_5, x_6);
lean_dec(x_142);
x_11 = x_143;
goto block_15;
}
}
}
}
block_15:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_2 = x_12;
x_3 = x_10;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_1);
return x_11;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_3, 0);
x_145 = lean_ctor_get(x_3, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_3);
lean_inc(x_1);
x_151 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_151, 0, x_1);
x_152 = lean_ctor_get(x_144, 1);
lean_inc(x_152);
lean_dec(x_144);
x_153 = lean_find_expr(x_151, x_152);
lean_dec(x_152);
lean_dec(x_151);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_153, x_4, x_5, x_6);
x_146 = x_154;
goto block_150;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
switch (lean_obj_tag(x_155)) {
case 0:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Expr_bvar___override(x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_160 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_159, x_4, x_5, x_6);
lean_dec(x_159);
x_146 = x_160;
goto block_150;
}
case 1:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_155, 0);
lean_inc(x_161);
lean_dec(x_155);
x_162 = l_Lean_Expr_fvar___override(x_161);
if (lean_is_scalar(x_156)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_156;
}
lean_ctor_set(x_163, 0, x_162);
x_164 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_163, x_4, x_5, x_6);
lean_dec(x_163);
x_146 = x_164;
goto block_150;
}
case 2:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_155, 0);
lean_inc(x_165);
lean_dec(x_155);
x_166 = l_Lean_Expr_mvar___override(x_165);
if (lean_is_scalar(x_156)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_156;
}
lean_ctor_set(x_167, 0, x_166);
x_168 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_167, x_4, x_5, x_6);
lean_dec(x_167);
x_146 = x_168;
goto block_150;
}
case 3:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_155, 0);
lean_inc(x_169);
lean_dec(x_155);
x_170 = l_Lean_Expr_sort___override(x_169);
if (lean_is_scalar(x_156)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_156;
}
lean_ctor_set(x_171, 0, x_170);
x_172 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_171, x_4, x_5, x_6);
lean_dec(x_171);
x_146 = x_172;
goto block_150;
}
case 4:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_156);
x_173 = lean_ctor_get(x_155, 0);
lean_inc(x_173);
lean_dec(x_155);
x_174 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_175 = l_Lean_stringToMessageData(x_174);
lean_dec(x_174);
x_176 = l_Lean_MessageData_ofName(x_173);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_179 = l_Lean_stringToMessageData(x_178);
lean_dec(x_178);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_180, x_4, x_5, x_6);
x_146 = x_181;
goto block_150;
}
case 5:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_155, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_155, 1);
lean_inc(x_183);
lean_dec(x_155);
x_184 = l_Lean_Expr_app___override(x_182, x_183);
if (lean_is_scalar(x_156)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_156;
}
lean_ctor_set(x_185, 0, x_184);
x_186 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_185, x_4, x_5, x_6);
lean_dec(x_185);
x_146 = x_186;
goto block_150;
}
case 6:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_155, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_155, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_155, 2);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_155, sizeof(void*)*3 + 8);
lean_dec(x_155);
x_191 = l_Lean_Expr_lam___override(x_187, x_188, x_189, x_190);
if (lean_is_scalar(x_156)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_156;
}
lean_ctor_set(x_192, 0, x_191);
x_193 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_192, x_4, x_5, x_6);
lean_dec(x_192);
x_146 = x_193;
goto block_150;
}
case 7:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_155, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_155, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_155, 2);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_155, sizeof(void*)*3 + 8);
lean_dec(x_155);
x_198 = l_Lean_Expr_forallE___override(x_194, x_195, x_196, x_197);
if (lean_is_scalar(x_156)) {
 x_199 = lean_alloc_ctor(1, 1, 0);
} else {
 x_199 = x_156;
}
lean_ctor_set(x_199, 0, x_198);
x_200 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_199, x_4, x_5, x_6);
lean_dec(x_199);
x_146 = x_200;
goto block_150;
}
case 8:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_155, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_155, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_155, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_155, 3);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_155, sizeof(void*)*4 + 8);
lean_dec(x_155);
x_206 = l_Lean_Expr_letE___override(x_201, x_202, x_203, x_204, x_205);
if (lean_is_scalar(x_156)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_156;
}
lean_ctor_set(x_207, 0, x_206);
x_208 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_207, x_4, x_5, x_6);
lean_dec(x_207);
x_146 = x_208;
goto block_150;
}
case 9:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_155, 0);
lean_inc(x_209);
lean_dec(x_155);
x_210 = l_Lean_Expr_lit___override(x_209);
if (lean_is_scalar(x_156)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_156;
}
lean_ctor_set(x_211, 0, x_210);
x_212 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_211, x_4, x_5, x_6);
lean_dec(x_211);
x_146 = x_212;
goto block_150;
}
case 10:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_155, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_155, 1);
lean_inc(x_214);
lean_dec(x_155);
x_215 = l_Lean_Expr_mdata___override(x_213, x_214);
if (lean_is_scalar(x_156)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_156;
}
lean_ctor_set(x_216, 0, x_215);
x_217 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_216, x_4, x_5, x_6);
lean_dec(x_216);
x_146 = x_217;
goto block_150;
}
default: 
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_218 = lean_ctor_get(x_155, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_155, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_155, 2);
lean_inc(x_220);
lean_dec(x_155);
x_221 = l_Lean_Expr_proj___override(x_218, x_219, x_220);
if (lean_is_scalar(x_156)) {
 x_222 = lean_alloc_ctor(1, 1, 0);
} else {
 x_222 = x_156;
}
lean_ctor_set(x_222, 0, x_221);
x_223 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_222, x_4, x_5, x_6);
lean_dec(x_222);
x_146 = x_223;
goto block_150;
}
}
}
block_150:
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_2 = x_147;
x_3 = x_145;
x_6 = x_148;
goto _start;
}
else
{
lean_dec(x_145);
lean_dec(x_1);
return x_146;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_find_expr(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_3);
x_19 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
x_11 = x_19;
goto block_15;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_bvar___override(x_22);
lean_ctor_set(x_18, 0, x_23);
x_24 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_24;
goto block_15;
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_3);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_Expr_fvar___override(x_25);
lean_ctor_set(x_18, 0, x_26);
x_27 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_27;
goto block_15;
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_3);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Lean_Expr_mvar___override(x_28);
lean_ctor_set(x_18, 0, x_29);
x_30 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_30;
goto block_15;
}
case 3:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_3);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = l_Lean_Expr_sort___override(x_31);
lean_ctor_set(x_18, 0, x_32);
x_33 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_33;
goto block_15;
}
case 4:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_18);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = l_Lean_MessageData_ofName(x_34);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_3, 0, x_36);
x_38 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_40, x_4, x_5, x_6);
x_11 = x_41;
goto block_15;
}
case 5:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_3);
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_dec(x_21);
x_44 = l_Lean_Expr_app___override(x_42, x_43);
lean_ctor_set(x_18, 0, x_44);
x_45 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_45;
goto block_15;
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_3);
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_21, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 8);
lean_dec(x_21);
x_50 = l_Lean_Expr_lam___override(x_46, x_47, x_48, x_49);
lean_ctor_set(x_18, 0, x_50);
x_51 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_51;
goto block_15;
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_3);
x_52 = lean_ctor_get(x_21, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 8);
lean_dec(x_21);
x_56 = l_Lean_Expr_forallE___override(x_52, x_53, x_54, x_55);
lean_ctor_set(x_18, 0, x_56);
x_57 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_57;
goto block_15;
}
case 8:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_3);
x_58 = lean_ctor_get(x_21, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_21, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_21, 3);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 8);
lean_dec(x_21);
x_63 = l_Lean_Expr_letE___override(x_58, x_59, x_60, x_61, x_62);
lean_ctor_set(x_18, 0, x_63);
x_64 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_64;
goto block_15;
}
case 9:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_3);
x_65 = lean_ctor_get(x_21, 0);
lean_inc(x_65);
lean_dec(x_21);
x_66 = l_Lean_Expr_lit___override(x_65);
lean_ctor_set(x_18, 0, x_66);
x_67 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_67;
goto block_15;
}
case 10:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_3);
x_68 = lean_ctor_get(x_21, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
lean_dec(x_21);
x_70 = l_Lean_Expr_mdata___override(x_68, x_69);
lean_ctor_set(x_18, 0, x_70);
x_71 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_71;
goto block_15;
}
default: 
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_3);
x_72 = lean_ctor_get(x_21, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_21, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_21, 2);
lean_inc(x_74);
lean_dec(x_21);
x_75 = l_Lean_Expr_proj___override(x_72, x_73, x_74);
lean_ctor_set(x_18, 0, x_75);
x_76 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_18, x_4, x_5, x_6);
lean_dec(x_18);
x_11 = x_76;
goto block_15;
}
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_18, 0);
lean_inc(x_77);
lean_dec(x_18);
switch (lean_obj_tag(x_77)) {
case 0:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_3);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Expr_bvar___override(x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_80, x_4, x_5, x_6);
lean_dec(x_80);
x_11 = x_81;
goto block_15;
}
case 1:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_free_object(x_3);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
lean_dec(x_77);
x_83 = l_Lean_Expr_fvar___override(x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_84, x_4, x_5, x_6);
lean_dec(x_84);
x_11 = x_85;
goto block_15;
}
case 2:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_3);
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
lean_dec(x_77);
x_87 = l_Lean_Expr_mvar___override(x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_88, x_4, x_5, x_6);
lean_dec(x_88);
x_11 = x_89;
goto block_15;
}
case 3:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_3);
x_90 = lean_ctor_get(x_77, 0);
lean_inc(x_90);
lean_dec(x_77);
x_91 = l_Lean_Expr_sort___override(x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_92, x_4, x_5, x_6);
lean_dec(x_92);
x_11 = x_93;
goto block_15;
}
case 4:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_77, 0);
lean_inc(x_94);
lean_dec(x_77);
x_95 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = l_Lean_MessageData_ofName(x_94);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_97);
lean_ctor_set(x_3, 0, x_96);
x_98 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_3);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_100, x_4, x_5, x_6);
x_11 = x_101;
goto block_15;
}
case 5:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_free_object(x_3);
x_102 = lean_ctor_get(x_77, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_77, 1);
lean_inc(x_103);
lean_dec(x_77);
x_104 = l_Lean_Expr_app___override(x_102, x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_105, x_4, x_5, x_6);
lean_dec(x_105);
x_11 = x_106;
goto block_15;
}
case 6:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_3);
x_107 = lean_ctor_get(x_77, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_77, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_77, 2);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_77, sizeof(void*)*3 + 8);
lean_dec(x_77);
x_111 = l_Lean_Expr_lam___override(x_107, x_108, x_109, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_112, x_4, x_5, x_6);
lean_dec(x_112);
x_11 = x_113;
goto block_15;
}
case 7:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_free_object(x_3);
x_114 = lean_ctor_get(x_77, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_77, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_77, 2);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_77, sizeof(void*)*3 + 8);
lean_dec(x_77);
x_118 = l_Lean_Expr_forallE___override(x_114, x_115, x_116, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_119, x_4, x_5, x_6);
lean_dec(x_119);
x_11 = x_120;
goto block_15;
}
case 8:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_free_object(x_3);
x_121 = lean_ctor_get(x_77, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_77, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_77, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_77, 3);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_77, sizeof(void*)*4 + 8);
lean_dec(x_77);
x_126 = l_Lean_Expr_letE___override(x_121, x_122, x_123, x_124, x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_127, x_4, x_5, x_6);
lean_dec(x_127);
x_11 = x_128;
goto block_15;
}
case 9:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_3);
x_129 = lean_ctor_get(x_77, 0);
lean_inc(x_129);
lean_dec(x_77);
x_130 = l_Lean_Expr_lit___override(x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_131, x_4, x_5, x_6);
lean_dec(x_131);
x_11 = x_132;
goto block_15;
}
case 10:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_free_object(x_3);
x_133 = lean_ctor_get(x_77, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_77, 1);
lean_inc(x_134);
lean_dec(x_77);
x_135 = l_Lean_Expr_mdata___override(x_133, x_134);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_136, x_4, x_5, x_6);
lean_dec(x_136);
x_11 = x_137;
goto block_15;
}
default: 
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_free_object(x_3);
x_138 = lean_ctor_get(x_77, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_77, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_77, 2);
lean_inc(x_140);
lean_dec(x_77);
x_141 = l_Lean_Expr_proj___override(x_138, x_139, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_142, x_4, x_5, x_6);
lean_dec(x_142);
x_11 = x_143;
goto block_15;
}
}
}
}
block_15:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2_spec__2(x_1, x_12, x_10, x_4, x_5, x_13);
return x_14;
}
else
{
lean_dec(x_10);
lean_dec(x_1);
return x_11;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_3, 0);
x_145 = lean_ctor_get(x_3, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_3);
lean_inc(x_1);
x_151 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_151, 0, x_1);
x_152 = lean_ctor_get(x_144, 1);
lean_inc(x_152);
lean_dec(x_144);
x_153 = lean_find_expr(x_151, x_152);
lean_dec(x_152);
lean_dec(x_151);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_153, x_4, x_5, x_6);
x_146 = x_154;
goto block_150;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
switch (lean_obj_tag(x_155)) {
case 0:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Expr_bvar___override(x_157);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
x_160 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_159, x_4, x_5, x_6);
lean_dec(x_159);
x_146 = x_160;
goto block_150;
}
case 1:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_155, 0);
lean_inc(x_161);
lean_dec(x_155);
x_162 = l_Lean_Expr_fvar___override(x_161);
if (lean_is_scalar(x_156)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_156;
}
lean_ctor_set(x_163, 0, x_162);
x_164 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_163, x_4, x_5, x_6);
lean_dec(x_163);
x_146 = x_164;
goto block_150;
}
case 2:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_155, 0);
lean_inc(x_165);
lean_dec(x_155);
x_166 = l_Lean_Expr_mvar___override(x_165);
if (lean_is_scalar(x_156)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_156;
}
lean_ctor_set(x_167, 0, x_166);
x_168 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_167, x_4, x_5, x_6);
lean_dec(x_167);
x_146 = x_168;
goto block_150;
}
case 3:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_155, 0);
lean_inc(x_169);
lean_dec(x_155);
x_170 = l_Lean_Expr_sort___override(x_169);
if (lean_is_scalar(x_156)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_156;
}
lean_ctor_set(x_171, 0, x_170);
x_172 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_171, x_4, x_5, x_6);
lean_dec(x_171);
x_146 = x_172;
goto block_150;
}
case 4:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_156);
x_173 = lean_ctor_get(x_155, 0);
lean_inc(x_173);
lean_dec(x_155);
x_174 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_175 = l_Lean_stringToMessageData(x_174);
lean_dec(x_174);
x_176 = l_Lean_MessageData_ofName(x_173);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_179 = l_Lean_stringToMessageData(x_178);
lean_dec(x_178);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_180, x_4, x_5, x_6);
x_146 = x_181;
goto block_150;
}
case 5:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_155, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_155, 1);
lean_inc(x_183);
lean_dec(x_155);
x_184 = l_Lean_Expr_app___override(x_182, x_183);
if (lean_is_scalar(x_156)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_156;
}
lean_ctor_set(x_185, 0, x_184);
x_186 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_185, x_4, x_5, x_6);
lean_dec(x_185);
x_146 = x_186;
goto block_150;
}
case 6:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_155, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_155, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_155, 2);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_155, sizeof(void*)*3 + 8);
lean_dec(x_155);
x_191 = l_Lean_Expr_lam___override(x_187, x_188, x_189, x_190);
if (lean_is_scalar(x_156)) {
 x_192 = lean_alloc_ctor(1, 1, 0);
} else {
 x_192 = x_156;
}
lean_ctor_set(x_192, 0, x_191);
x_193 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_192, x_4, x_5, x_6);
lean_dec(x_192);
x_146 = x_193;
goto block_150;
}
case 7:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_155, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_155, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_155, 2);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_155, sizeof(void*)*3 + 8);
lean_dec(x_155);
x_198 = l_Lean_Expr_forallE___override(x_194, x_195, x_196, x_197);
if (lean_is_scalar(x_156)) {
 x_199 = lean_alloc_ctor(1, 1, 0);
} else {
 x_199 = x_156;
}
lean_ctor_set(x_199, 0, x_198);
x_200 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_199, x_4, x_5, x_6);
lean_dec(x_199);
x_146 = x_200;
goto block_150;
}
case 8:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_155, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_155, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_155, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_155, 3);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_155, sizeof(void*)*4 + 8);
lean_dec(x_155);
x_206 = l_Lean_Expr_letE___override(x_201, x_202, x_203, x_204, x_205);
if (lean_is_scalar(x_156)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_156;
}
lean_ctor_set(x_207, 0, x_206);
x_208 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_207, x_4, x_5, x_6);
lean_dec(x_207);
x_146 = x_208;
goto block_150;
}
case 9:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_155, 0);
lean_inc(x_209);
lean_dec(x_155);
x_210 = l_Lean_Expr_lit___override(x_209);
if (lean_is_scalar(x_156)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_156;
}
lean_ctor_set(x_211, 0, x_210);
x_212 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_211, x_4, x_5, x_6);
lean_dec(x_211);
x_146 = x_212;
goto block_150;
}
case 10:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_155, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_155, 1);
lean_inc(x_214);
lean_dec(x_155);
x_215 = l_Lean_Expr_mdata___override(x_213, x_214);
if (lean_is_scalar(x_156)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_156;
}
lean_ctor_set(x_216, 0, x_215);
x_217 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_216, x_4, x_5, x_6);
lean_dec(x_216);
x_146 = x_217;
goto block_150;
}
default: 
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_218 = lean_ctor_get(x_155, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_155, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_155, 2);
lean_inc(x_220);
lean_dec(x_155);
x_221 = l_Lean_Expr_proj___override(x_218, x_219, x_220);
if (lean_is_scalar(x_156)) {
 x_222 = lean_alloc_ctor(1, 1, 0);
} else {
 x_222 = x_156;
}
lean_ctor_set(x_222, 0, x_221);
x_223 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_222, x_4, x_5, x_6);
lean_dec(x_222);
x_146 = x_223;
goto block_150;
}
}
}
block_150:
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2_spec__2(x_1, x_147, x_145, x_4, x_5, x_148);
return x_149;
}
else
{
lean_dec(x_145);
lean_dec(x_1);
return x_146;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
x_22 = lean_find_expr(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_free_object(x_3);
x_23 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
x_11 = x_23;
goto block_19;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Expr_bvar___override(x_26);
lean_ctor_set(x_22, 0, x_27);
x_28 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_28;
goto block_19;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_3);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Expr_fvar___override(x_29);
lean_ctor_set(x_22, 0, x_30);
x_31 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_31;
goto block_19;
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_3);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l_Lean_Expr_mvar___override(x_32);
lean_ctor_set(x_22, 0, x_33);
x_34 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_34;
goto block_19;
}
case 3:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_3);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = l_Lean_Expr_sort___override(x_35);
lean_ctor_set(x_22, 0, x_36);
x_37 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_37;
goto block_19;
}
case 4:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_22);
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_MessageData_ofName(x_38);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_40);
x_42 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_44, x_4, x_5, x_6);
x_11 = x_45;
goto block_19;
}
case 5:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_3);
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
x_48 = l_Lean_Expr_app___override(x_46, x_47);
lean_ctor_set(x_22, 0, x_48);
x_49 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_49;
goto block_19;
}
case 6:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_3);
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_25, 2);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
lean_dec(x_25);
x_54 = l_Lean_Expr_lam___override(x_50, x_51, x_52, x_53);
lean_ctor_set(x_22, 0, x_54);
x_55 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_55;
goto block_19;
}
case 7:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_3);
x_56 = lean_ctor_get(x_25, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_25, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_25, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
lean_dec(x_25);
x_60 = l_Lean_Expr_forallE___override(x_56, x_57, x_58, x_59);
lean_ctor_set(x_22, 0, x_60);
x_61 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_61;
goto block_19;
}
case 8:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_3);
x_62 = lean_ctor_get(x_25, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_25, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_25, 3);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_25, sizeof(void*)*4 + 8);
lean_dec(x_25);
x_67 = l_Lean_Expr_letE___override(x_62, x_63, x_64, x_65, x_66);
lean_ctor_set(x_22, 0, x_67);
x_68 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_68;
goto block_19;
}
case 9:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_3);
x_69 = lean_ctor_get(x_25, 0);
lean_inc(x_69);
lean_dec(x_25);
x_70 = l_Lean_Expr_lit___override(x_69);
lean_ctor_set(x_22, 0, x_70);
x_71 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_71;
goto block_19;
}
case 10:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_3);
x_72 = lean_ctor_get(x_25, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_dec(x_25);
x_74 = l_Lean_Expr_mdata___override(x_72, x_73);
lean_ctor_set(x_22, 0, x_74);
x_75 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_75;
goto block_19;
}
default: 
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_3);
x_76 = lean_ctor_get(x_25, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_25, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_25, 2);
lean_inc(x_78);
lean_dec(x_25);
x_79 = l_Lean_Expr_proj___override(x_76, x_77, x_78);
lean_ctor_set(x_22, 0, x_79);
x_80 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_80;
goto block_19;
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_22, 0);
lean_inc(x_81);
lean_dec(x_22);
switch (lean_obj_tag(x_81)) {
case 0:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_free_object(x_3);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_Expr_bvar___override(x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_84, x_4, x_5, x_6);
lean_dec(x_84);
x_11 = x_85;
goto block_19;
}
case 1:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_3);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
lean_dec(x_81);
x_87 = l_Lean_Expr_fvar___override(x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_88, x_4, x_5, x_6);
lean_dec(x_88);
x_11 = x_89;
goto block_19;
}
case 2:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_3);
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
lean_dec(x_81);
x_91 = l_Lean_Expr_mvar___override(x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_92, x_4, x_5, x_6);
lean_dec(x_92);
x_11 = x_93;
goto block_19;
}
case 3:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_3);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
lean_dec(x_81);
x_95 = l_Lean_Expr_sort___override(x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_96, x_4, x_5, x_6);
lean_dec(x_96);
x_11 = x_97;
goto block_19;
}
case 4:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_81, 0);
lean_inc(x_98);
lean_dec(x_81);
x_99 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = l_Lean_MessageData_ofName(x_98);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_101);
lean_ctor_set(x_3, 0, x_100);
x_102 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_3);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_104, x_4, x_5, x_6);
x_11 = x_105;
goto block_19;
}
case 5:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_3);
x_106 = lean_ctor_get(x_81, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_81, 1);
lean_inc(x_107);
lean_dec(x_81);
x_108 = l_Lean_Expr_app___override(x_106, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_109, x_4, x_5, x_6);
lean_dec(x_109);
x_11 = x_110;
goto block_19;
}
case 6:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_free_object(x_3);
x_111 = lean_ctor_get(x_81, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_81, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_81, 2);
lean_inc(x_113);
x_114 = lean_ctor_get_uint8(x_81, sizeof(void*)*3 + 8);
lean_dec(x_81);
x_115 = l_Lean_Expr_lam___override(x_111, x_112, x_113, x_114);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_116, x_4, x_5, x_6);
lean_dec(x_116);
x_11 = x_117;
goto block_19;
}
case 7:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_free_object(x_3);
x_118 = lean_ctor_get(x_81, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_81, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_81, 2);
lean_inc(x_120);
x_121 = lean_ctor_get_uint8(x_81, sizeof(void*)*3 + 8);
lean_dec(x_81);
x_122 = l_Lean_Expr_forallE___override(x_118, x_119, x_120, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_123, x_4, x_5, x_6);
lean_dec(x_123);
x_11 = x_124;
goto block_19;
}
case 8:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_3);
x_125 = lean_ctor_get(x_81, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_81, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_81, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_81, 3);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_81, sizeof(void*)*4 + 8);
lean_dec(x_81);
x_130 = l_Lean_Expr_letE___override(x_125, x_126, x_127, x_128, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_131, x_4, x_5, x_6);
lean_dec(x_131);
x_11 = x_132;
goto block_19;
}
case 9:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_free_object(x_3);
x_133 = lean_ctor_get(x_81, 0);
lean_inc(x_133);
lean_dec(x_81);
x_134 = l_Lean_Expr_lit___override(x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_135, x_4, x_5, x_6);
lean_dec(x_135);
x_11 = x_136;
goto block_19;
}
case 10:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_free_object(x_3);
x_137 = lean_ctor_get(x_81, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_81, 1);
lean_inc(x_138);
lean_dec(x_81);
x_139 = l_Lean_Expr_mdata___override(x_137, x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_140, x_4, x_5, x_6);
lean_dec(x_140);
x_11 = x_141;
goto block_19;
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_free_object(x_3);
x_142 = lean_ctor_get(x_81, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_81, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_81, 2);
lean_inc(x_144);
lean_dec(x_81);
x_145 = l_Lean_Expr_proj___override(x_142, x_143, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_146, x_4, x_5, x_6);
lean_dec(x_146);
x_11 = x_147;
goto block_19;
}
}
}
}
block_19:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
lean_dec(x_9);
lean_inc(x_1);
x_15 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(x_1, x_12, x_14, x_4, x_5, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_10;
x_6 = x_17;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_11;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_148 = lean_ctor_get(x_3, 0);
x_149 = lean_ctor_get(x_3, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_3);
lean_inc(x_1);
x_159 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_159, 0, x_1);
x_160 = lean_ctor_get(x_148, 1);
lean_inc(x_160);
x_161 = lean_find_expr(x_159, x_160);
lean_dec(x_160);
lean_dec(x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_161, x_4, x_5, x_6);
x_150 = x_162;
goto block_158;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
switch (lean_obj_tag(x_163)) {
case 0:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Expr_bvar___override(x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_166);
x_168 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_167, x_4, x_5, x_6);
lean_dec(x_167);
x_150 = x_168;
goto block_158;
}
case 1:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_163, 0);
lean_inc(x_169);
lean_dec(x_163);
x_170 = l_Lean_Expr_fvar___override(x_169);
if (lean_is_scalar(x_164)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_164;
}
lean_ctor_set(x_171, 0, x_170);
x_172 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_171, x_4, x_5, x_6);
lean_dec(x_171);
x_150 = x_172;
goto block_158;
}
case 2:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_163, 0);
lean_inc(x_173);
lean_dec(x_163);
x_174 = l_Lean_Expr_mvar___override(x_173);
if (lean_is_scalar(x_164)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_164;
}
lean_ctor_set(x_175, 0, x_174);
x_176 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_175, x_4, x_5, x_6);
lean_dec(x_175);
x_150 = x_176;
goto block_158;
}
case 3:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_163, 0);
lean_inc(x_177);
lean_dec(x_163);
x_178 = l_Lean_Expr_sort___override(x_177);
if (lean_is_scalar(x_164)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_164;
}
lean_ctor_set(x_179, 0, x_178);
x_180 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_179, x_4, x_5, x_6);
lean_dec(x_179);
x_150 = x_180;
goto block_158;
}
case 4:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_164);
x_181 = lean_ctor_get(x_163, 0);
lean_inc(x_181);
lean_dec(x_163);
x_182 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_183 = l_Lean_stringToMessageData(x_182);
lean_dec(x_182);
x_184 = l_Lean_MessageData_ofName(x_181);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_187 = l_Lean_stringToMessageData(x_186);
lean_dec(x_186);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_188, x_4, x_5, x_6);
x_150 = x_189;
goto block_158;
}
case 5:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_163, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_163, 1);
lean_inc(x_191);
lean_dec(x_163);
x_192 = l_Lean_Expr_app___override(x_190, x_191);
if (lean_is_scalar(x_164)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_164;
}
lean_ctor_set(x_193, 0, x_192);
x_194 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_193, x_4, x_5, x_6);
lean_dec(x_193);
x_150 = x_194;
goto block_158;
}
case 6:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = lean_ctor_get(x_163, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_163, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_163, 2);
lean_inc(x_197);
x_198 = lean_ctor_get_uint8(x_163, sizeof(void*)*3 + 8);
lean_dec(x_163);
x_199 = l_Lean_Expr_lam___override(x_195, x_196, x_197, x_198);
if (lean_is_scalar(x_164)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_164;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_200, x_4, x_5, x_6);
lean_dec(x_200);
x_150 = x_201;
goto block_158;
}
case 7:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_163, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_163, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_163, 2);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_163, sizeof(void*)*3 + 8);
lean_dec(x_163);
x_206 = l_Lean_Expr_forallE___override(x_202, x_203, x_204, x_205);
if (lean_is_scalar(x_164)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_164;
}
lean_ctor_set(x_207, 0, x_206);
x_208 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_207, x_4, x_5, x_6);
lean_dec(x_207);
x_150 = x_208;
goto block_158;
}
case 8:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_209 = lean_ctor_get(x_163, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_163, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_163, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_163, 3);
lean_inc(x_212);
x_213 = lean_ctor_get_uint8(x_163, sizeof(void*)*4 + 8);
lean_dec(x_163);
x_214 = l_Lean_Expr_letE___override(x_209, x_210, x_211, x_212, x_213);
if (lean_is_scalar(x_164)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_164;
}
lean_ctor_set(x_215, 0, x_214);
x_216 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_215, x_4, x_5, x_6);
lean_dec(x_215);
x_150 = x_216;
goto block_158;
}
case 9:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_163, 0);
lean_inc(x_217);
lean_dec(x_163);
x_218 = l_Lean_Expr_lit___override(x_217);
if (lean_is_scalar(x_164)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_164;
}
lean_ctor_set(x_219, 0, x_218);
x_220 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_219, x_4, x_5, x_6);
lean_dec(x_219);
x_150 = x_220;
goto block_158;
}
case 10:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_163, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_163, 1);
lean_inc(x_222);
lean_dec(x_163);
x_223 = l_Lean_Expr_mdata___override(x_221, x_222);
if (lean_is_scalar(x_164)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_164;
}
lean_ctor_set(x_224, 0, x_223);
x_225 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_224, x_4, x_5, x_6);
lean_dec(x_224);
x_150 = x_225;
goto block_158;
}
default: 
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_163, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_163, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_163, 2);
lean_inc(x_228);
lean_dec(x_163);
x_229 = l_Lean_Expr_proj___override(x_226, x_227, x_228);
if (lean_is_scalar(x_164)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_164;
}
lean_ctor_set(x_230, 0, x_229);
x_231 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_230, x_4, x_5, x_6);
lean_dec(x_230);
x_150 = x_231;
goto block_158;
}
}
}
block_158:
{
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_148, 2);
lean_inc(x_153);
lean_dec(x_148);
lean_inc(x_1);
x_154 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(x_1, x_151, x_153, x_4, x_5, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_2 = x_155;
x_3 = x_149;
x_6 = x_156;
goto _start;
}
else
{
lean_dec(x_149);
lean_dec(x_1);
return x_154;
}
}
else
{
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_1);
return x_150;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
x_22 = lean_find_expr(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_free_object(x_3);
x_23 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
x_11 = x_23;
goto block_19;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Expr_bvar___override(x_26);
lean_ctor_set(x_22, 0, x_27);
x_28 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_28;
goto block_19;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_3);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Expr_fvar___override(x_29);
lean_ctor_set(x_22, 0, x_30);
x_31 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_31;
goto block_19;
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_3);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l_Lean_Expr_mvar___override(x_32);
lean_ctor_set(x_22, 0, x_33);
x_34 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_34;
goto block_19;
}
case 3:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_3);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = l_Lean_Expr_sort___override(x_35);
lean_ctor_set(x_22, 0, x_36);
x_37 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_37;
goto block_19;
}
case 4:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_22);
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_MessageData_ofName(x_38);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_40);
x_42 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_44, x_4, x_5, x_6);
x_11 = x_45;
goto block_19;
}
case 5:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_3);
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
x_48 = l_Lean_Expr_app___override(x_46, x_47);
lean_ctor_set(x_22, 0, x_48);
x_49 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_49;
goto block_19;
}
case 6:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_3);
x_50 = lean_ctor_get(x_25, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_25, 2);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
lean_dec(x_25);
x_54 = l_Lean_Expr_lam___override(x_50, x_51, x_52, x_53);
lean_ctor_set(x_22, 0, x_54);
x_55 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_55;
goto block_19;
}
case 7:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_3);
x_56 = lean_ctor_get(x_25, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_25, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_25, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
lean_dec(x_25);
x_60 = l_Lean_Expr_forallE___override(x_56, x_57, x_58, x_59);
lean_ctor_set(x_22, 0, x_60);
x_61 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_61;
goto block_19;
}
case 8:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_3);
x_62 = lean_ctor_get(x_25, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_25, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_25, 3);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_25, sizeof(void*)*4 + 8);
lean_dec(x_25);
x_67 = l_Lean_Expr_letE___override(x_62, x_63, x_64, x_65, x_66);
lean_ctor_set(x_22, 0, x_67);
x_68 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_68;
goto block_19;
}
case 9:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_3);
x_69 = lean_ctor_get(x_25, 0);
lean_inc(x_69);
lean_dec(x_25);
x_70 = l_Lean_Expr_lit___override(x_69);
lean_ctor_set(x_22, 0, x_70);
x_71 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_71;
goto block_19;
}
case 10:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_3);
x_72 = lean_ctor_get(x_25, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_dec(x_25);
x_74 = l_Lean_Expr_mdata___override(x_72, x_73);
lean_ctor_set(x_22, 0, x_74);
x_75 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_75;
goto block_19;
}
default: 
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_3);
x_76 = lean_ctor_get(x_25, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_25, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_25, 2);
lean_inc(x_78);
lean_dec(x_25);
x_79 = l_Lean_Expr_proj___override(x_76, x_77, x_78);
lean_ctor_set(x_22, 0, x_79);
x_80 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_22, x_4, x_5, x_6);
lean_dec(x_22);
x_11 = x_80;
goto block_19;
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_22, 0);
lean_inc(x_81);
lean_dec(x_22);
switch (lean_obj_tag(x_81)) {
case 0:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_free_object(x_3);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_Expr_bvar___override(x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_84, x_4, x_5, x_6);
lean_dec(x_84);
x_11 = x_85;
goto block_19;
}
case 1:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_3);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
lean_dec(x_81);
x_87 = l_Lean_Expr_fvar___override(x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_88, x_4, x_5, x_6);
lean_dec(x_88);
x_11 = x_89;
goto block_19;
}
case 2:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_3);
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
lean_dec(x_81);
x_91 = l_Lean_Expr_mvar___override(x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_92, x_4, x_5, x_6);
lean_dec(x_92);
x_11 = x_93;
goto block_19;
}
case 3:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_3);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
lean_dec(x_81);
x_95 = l_Lean_Expr_sort___override(x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_96, x_4, x_5, x_6);
lean_dec(x_96);
x_11 = x_97;
goto block_19;
}
case 4:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_81, 0);
lean_inc(x_98);
lean_dec(x_81);
x_99 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = l_Lean_MessageData_ofName(x_98);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_101);
lean_ctor_set(x_3, 0, x_100);
x_102 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_3);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_104, x_4, x_5, x_6);
x_11 = x_105;
goto block_19;
}
case 5:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_3);
x_106 = lean_ctor_get(x_81, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_81, 1);
lean_inc(x_107);
lean_dec(x_81);
x_108 = l_Lean_Expr_app___override(x_106, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_109, x_4, x_5, x_6);
lean_dec(x_109);
x_11 = x_110;
goto block_19;
}
case 6:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_free_object(x_3);
x_111 = lean_ctor_get(x_81, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_81, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_81, 2);
lean_inc(x_113);
x_114 = lean_ctor_get_uint8(x_81, sizeof(void*)*3 + 8);
lean_dec(x_81);
x_115 = l_Lean_Expr_lam___override(x_111, x_112, x_113, x_114);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_116, x_4, x_5, x_6);
lean_dec(x_116);
x_11 = x_117;
goto block_19;
}
case 7:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_free_object(x_3);
x_118 = lean_ctor_get(x_81, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_81, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_81, 2);
lean_inc(x_120);
x_121 = lean_ctor_get_uint8(x_81, sizeof(void*)*3 + 8);
lean_dec(x_81);
x_122 = l_Lean_Expr_forallE___override(x_118, x_119, x_120, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_123, x_4, x_5, x_6);
lean_dec(x_123);
x_11 = x_124;
goto block_19;
}
case 8:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_3);
x_125 = lean_ctor_get(x_81, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_81, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_81, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_81, 3);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_81, sizeof(void*)*4 + 8);
lean_dec(x_81);
x_130 = l_Lean_Expr_letE___override(x_125, x_126, x_127, x_128, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_131, x_4, x_5, x_6);
lean_dec(x_131);
x_11 = x_132;
goto block_19;
}
case 9:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_free_object(x_3);
x_133 = lean_ctor_get(x_81, 0);
lean_inc(x_133);
lean_dec(x_81);
x_134 = l_Lean_Expr_lit___override(x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_135, x_4, x_5, x_6);
lean_dec(x_135);
x_11 = x_136;
goto block_19;
}
case 10:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_free_object(x_3);
x_137 = lean_ctor_get(x_81, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_81, 1);
lean_inc(x_138);
lean_dec(x_81);
x_139 = l_Lean_Expr_mdata___override(x_137, x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_140, x_4, x_5, x_6);
lean_dec(x_140);
x_11 = x_141;
goto block_19;
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_free_object(x_3);
x_142 = lean_ctor_get(x_81, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_81, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_81, 2);
lean_inc(x_144);
lean_dec(x_81);
x_145 = l_Lean_Expr_proj___override(x_142, x_143, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_146, x_4, x_5, x_6);
lean_dec(x_146);
x_11 = x_147;
goto block_19;
}
}
}
}
block_19:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
lean_dec(x_9);
lean_inc(x_1);
x_15 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(x_1, x_12, x_14, x_4, x_5, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4_spec__4(x_1, x_16, x_10, x_4, x_5, x_17);
return x_18;
}
else
{
lean_dec(x_10);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_11;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_148 = lean_ctor_get(x_3, 0);
x_149 = lean_ctor_get(x_3, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_3);
lean_inc(x_1);
x_159 = lean_alloc_closure((void*)(l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_159, 0, x_1);
x_160 = lean_ctor_get(x_148, 1);
lean_inc(x_160);
x_161 = lean_find_expr(x_159, x_160);
lean_dec(x_160);
lean_dec(x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_161, x_4, x_5, x_6);
x_150 = x_162;
goto block_158;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
switch (lean_obj_tag(x_163)) {
case 0:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Expr_bvar___override(x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_166);
x_168 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_167, x_4, x_5, x_6);
lean_dec(x_167);
x_150 = x_168;
goto block_158;
}
case 1:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_163, 0);
lean_inc(x_169);
lean_dec(x_163);
x_170 = l_Lean_Expr_fvar___override(x_169);
if (lean_is_scalar(x_164)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_164;
}
lean_ctor_set(x_171, 0, x_170);
x_172 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_171, x_4, x_5, x_6);
lean_dec(x_171);
x_150 = x_172;
goto block_158;
}
case 2:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_163, 0);
lean_inc(x_173);
lean_dec(x_163);
x_174 = l_Lean_Expr_mvar___override(x_173);
if (lean_is_scalar(x_164)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_164;
}
lean_ctor_set(x_175, 0, x_174);
x_176 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_175, x_4, x_5, x_6);
lean_dec(x_175);
x_150 = x_176;
goto block_158;
}
case 3:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_163, 0);
lean_inc(x_177);
lean_dec(x_163);
x_178 = l_Lean_Expr_sort___override(x_177);
if (lean_is_scalar(x_164)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_164;
}
lean_ctor_set(x_179, 0, x_178);
x_180 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_179, x_4, x_5, x_6);
lean_dec(x_179);
x_150 = x_180;
goto block_158;
}
case 4:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_164);
x_181 = lean_ctor_get(x_163, 0);
lean_inc(x_181);
lean_dec(x_163);
x_182 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_183 = l_Lean_stringToMessageData(x_182);
lean_dec(x_182);
x_184 = l_Lean_MessageData_ofName(x_181);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_187 = l_Lean_stringToMessageData(x_186);
lean_dec(x_186);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_188, x_4, x_5, x_6);
x_150 = x_189;
goto block_158;
}
case 5:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_163, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_163, 1);
lean_inc(x_191);
lean_dec(x_163);
x_192 = l_Lean_Expr_app___override(x_190, x_191);
if (lean_is_scalar(x_164)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_164;
}
lean_ctor_set(x_193, 0, x_192);
x_194 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_193, x_4, x_5, x_6);
lean_dec(x_193);
x_150 = x_194;
goto block_158;
}
case 6:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = lean_ctor_get(x_163, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_163, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_163, 2);
lean_inc(x_197);
x_198 = lean_ctor_get_uint8(x_163, sizeof(void*)*3 + 8);
lean_dec(x_163);
x_199 = l_Lean_Expr_lam___override(x_195, x_196, x_197, x_198);
if (lean_is_scalar(x_164)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_164;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_200, x_4, x_5, x_6);
lean_dec(x_200);
x_150 = x_201;
goto block_158;
}
case 7:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_163, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_163, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_163, 2);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_163, sizeof(void*)*3 + 8);
lean_dec(x_163);
x_206 = l_Lean_Expr_forallE___override(x_202, x_203, x_204, x_205);
if (lean_is_scalar(x_164)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_164;
}
lean_ctor_set(x_207, 0, x_206);
x_208 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_207, x_4, x_5, x_6);
lean_dec(x_207);
x_150 = x_208;
goto block_158;
}
case 8:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_209 = lean_ctor_get(x_163, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_163, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_163, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_163, 3);
lean_inc(x_212);
x_213 = lean_ctor_get_uint8(x_163, sizeof(void*)*4 + 8);
lean_dec(x_163);
x_214 = l_Lean_Expr_letE___override(x_209, x_210, x_211, x_212, x_213);
if (lean_is_scalar(x_164)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_164;
}
lean_ctor_set(x_215, 0, x_214);
x_216 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_215, x_4, x_5, x_6);
lean_dec(x_215);
x_150 = x_216;
goto block_158;
}
case 9:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_163, 0);
lean_inc(x_217);
lean_dec(x_163);
x_218 = l_Lean_Expr_lit___override(x_217);
if (lean_is_scalar(x_164)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_164;
}
lean_ctor_set(x_219, 0, x_218);
x_220 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_219, x_4, x_5, x_6);
lean_dec(x_219);
x_150 = x_220;
goto block_158;
}
case 10:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_163, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_163, 1);
lean_inc(x_222);
lean_dec(x_163);
x_223 = l_Lean_Expr_mdata___override(x_221, x_222);
if (lean_is_scalar(x_164)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_164;
}
lean_ctor_set(x_224, 0, x_223);
x_225 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_224, x_4, x_5, x_6);
lean_dec(x_224);
x_150 = x_225;
goto block_158;
}
default: 
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_163, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_163, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_163, 2);
lean_inc(x_228);
lean_dec(x_163);
x_229 = l_Lean_Expr_proj___override(x_226, x_227, x_228);
if (lean_is_scalar(x_164)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_164;
}
lean_ctor_set(x_230, 0, x_229);
x_231 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_230, x_4, x_5, x_6);
lean_dec(x_230);
x_150 = x_231;
goto block_158;
}
}
}
block_158:
{
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_148, 2);
lean_inc(x_153);
lean_dec(x_148);
lean_inc(x_1);
x_154 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(x_1, x_151, x_153, x_4, x_5, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4_spec__4(x_1, x_155, x_149, x_4, x_5, x_156);
return x_157;
}
else
{
lean_dec(x_149);
lean_dec(x_1);
return x_154;
}
}
else
{
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_1);
return x_150;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_13; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_15 = lean_is_aux_recursor(x_1, x_3);
if (x_15 == 0)
{
x_13 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_isCasesOnRecursor(x_1, x_3);
if (x_16 == 0)
{
x_13 = x_15;
goto block_14;
}
else
{
goto block_12;
}
}
block_10:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_CoreM_0__Lean_supportedRecursors;
x_5 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
block_12:
{
uint8_t x_11; 
lean_inc(x_3);
x_11 = l_Lean_isRecCore(x_1, x_3);
if (x_11 == 0)
{
lean_dec(x_3);
return x_11;
}
else
{
goto block_10;
}
}
block_14:
{
if (x_13 == 0)
{
goto block_12;
}
else
{
lean_dec(x_1);
goto block_10;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_find_expr(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Expr_bvar___override(x_12);
lean_ctor_set(x_8, 0, x_13);
x_14 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Lean_Expr_fvar___override(x_15);
lean_ctor_set(x_8, 0, x_16);
x_17 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = l_Lean_Expr_mvar___override(x_18);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_Expr_sort___override(x_21);
lean_ctor_set(x_8, 0, x_22);
x_23 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_8);
lean_dec(x_2);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_MessageData_ofName(x_24);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_31, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_32;
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_dec(x_11);
x_35 = l_Lean_Expr_app___override(x_33, x_34);
lean_ctor_set(x_8, 0, x_35);
x_36 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_36;
}
case 6:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 2);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_41 = l_Lean_Expr_lam___override(x_37, x_38, x_39, x_40);
lean_ctor_set(x_8, 0, x_41);
x_42 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_42;
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_11, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 8);
lean_dec(x_11);
x_47 = l_Lean_Expr_forallE___override(x_43, x_44, x_45, x_46);
lean_ctor_set(x_8, 0, x_47);
x_48 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_48;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_11, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_11, 3);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_11, sizeof(void*)*4 + 8);
lean_dec(x_11);
x_54 = l_Lean_Expr_letE___override(x_49, x_50, x_51, x_52, x_53);
lean_ctor_set(x_8, 0, x_54);
x_55 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_55;
}
case 9:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
lean_dec(x_11);
x_57 = l_Lean_Expr_lit___override(x_56);
lean_ctor_set(x_8, 0, x_57);
x_58 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_58;
}
case 10:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_dec(x_11);
x_61 = l_Lean_Expr_mdata___override(x_59, x_60);
lean_ctor_set(x_8, 0, x_61);
x_62 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_62;
}
default: 
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_11, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_11, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_11, 2);
lean_inc(x_65);
lean_dec(x_11);
x_66 = l_Lean_Expr_proj___override(x_63, x_64, x_65);
lean_ctor_set(x_8, 0, x_66);
x_67 = lean_apply_4(x_2, x_8, x_5, x_6, x_7);
return x_67;
}
}
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_8, 0);
lean_inc(x_68);
lean_dec(x_8);
switch (lean_obj_tag(x_68)) {
case 0:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Expr_bvar___override(x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_apply_4(x_2, x_71, x_5, x_6, x_7);
return x_72;
}
case 1:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
x_74 = l_Lean_Expr_fvar___override(x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_apply_4(x_2, x_75, x_5, x_6, x_7);
return x_76;
}
case 2:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_68, 0);
lean_inc(x_77);
lean_dec(x_68);
x_78 = l_Lean_Expr_mvar___override(x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_apply_4(x_2, x_79, x_5, x_6, x_7);
return x_80;
}
case 3:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_68, 0);
lean_inc(x_81);
lean_dec(x_68);
x_82 = l_Lean_Expr_sort___override(x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_apply_4(x_2, x_83, x_5, x_6, x_7);
return x_84;
}
case 4:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
x_85 = lean_ctor_get(x_68, 0);
lean_inc(x_85);
lean_dec(x_68);
x_86 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
x_88 = l_Lean_MessageData_ofName(x_85);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_92, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_93;
}
case 5:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_68, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_68, 1);
lean_inc(x_95);
lean_dec(x_68);
x_96 = l_Lean_Expr_app___override(x_94, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_apply_4(x_2, x_97, x_5, x_6, x_7);
return x_98;
}
case 6:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_68, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_68, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_68, 2);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_68, sizeof(void*)*3 + 8);
lean_dec(x_68);
x_103 = l_Lean_Expr_lam___override(x_99, x_100, x_101, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_apply_4(x_2, x_104, x_5, x_6, x_7);
return x_105;
}
case 7:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_68, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_68, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_68, 2);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_68, sizeof(void*)*3 + 8);
lean_dec(x_68);
x_110 = l_Lean_Expr_forallE___override(x_106, x_107, x_108, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_apply_4(x_2, x_111, x_5, x_6, x_7);
return x_112;
}
case 8:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_68, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_68, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_68, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_68, 3);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_68, sizeof(void*)*4 + 8);
lean_dec(x_68);
x_118 = l_Lean_Expr_letE___override(x_113, x_114, x_115, x_116, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_apply_4(x_2, x_119, x_5, x_6, x_7);
return x_120;
}
case 9:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_68, 0);
lean_inc(x_121);
lean_dec(x_68);
x_122 = l_Lean_Expr_lit___override(x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_apply_4(x_2, x_123, x_5, x_6, x_7);
return x_124;
}
case 10:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_68, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_68, 1);
lean_inc(x_126);
lean_dec(x_68);
x_127 = l_Lean_Expr_mdata___override(x_125, x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_apply_4(x_2, x_128, x_5, x_6, x_7);
return x_129;
}
default: 
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_68, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_68, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_68, 2);
lean_inc(x_132);
lean_dec(x_68);
x_133 = l_Lean_Expr_proj___override(x_130, x_131, x_132);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_apply_4(x_2, x_134, x_5, x_6, x_7);
return x_135;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__1___boxed), 4, 0);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__2(x_7, x_8, x_3, x_11, x_4, x_5, x_6);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_7);
return x_12;
}
case 4:
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1(x_1, x_3, x_14, x_4, x_5, x_6);
lean_dec(x_14);
return x_15;
}
case 6:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4(x_1, x_3, x_16, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_8);
x_22 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__2(x_7, x_8, x_3, x_21, x_4, x_5, x_6);
lean_dec(x_21);
lean_dec(x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__2(x_7, x_8, x_23, x_20, x_4, x_5, x_24);
lean_dec(x_20);
lean_dec(x_23);
lean_dec(x_7);
return x_25;
}
else
{
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1(x_8, x_1, x_9, x_2, x_3, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l_Lean_Kernel_Exception_toMessageData(x_1, x_6);
x_8 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_7, x_3, x_4, x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 16)
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = l_Lean_throwInterruptException___at___Lean_Core_checkSystem_spec__0___redArg(x_4);
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
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(x_1, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_12);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_12);
x_13 = lean_ctor_get(x_6, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 7);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_10);
lean_ctor_set(x_16, 4, x_4);
lean_ctor_set(x_16, 5, x_13);
lean_ctor_set(x_16, 6, x_14);
lean_ctor_set(x_16, 7, x_15);
x_17 = lean_st_ref_set(x_2, x_16, x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_4);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 3);
lean_inc(x_28);
x_29 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_ctor_get(x_24, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_24, 7);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_33);
lean_ctor_set(x_35, 7, x_34);
x_36 = lean_st_ref_set(x_2, x_35, x_25);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_compileDecls_doCompile___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_mk_string_unchecked("compiling old: ", 15, 15);
x_7 = l_Lean_stringToMessageData(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_1, x_8);
x_10 = l_Lean_MessageData_ofList(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_compile_decls(x_9, x_1, x_2);
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
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_compile_decls(x_13, x_1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Environment_constants(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_1);
x_14 = l_List_all___redArg(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_7);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = l_Lean_compiler_enableNew;
x_18 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__1___boxed), 5, 1);
lean_closure_set(x_19, 0, x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__2___boxed), 5, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_1);
x_21 = lean_mk_string_unchecked("compiler", 8, 8);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_22, x_19, x_20, x_14, x_23, x_4, x_5, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 12)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_24, 1);
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
if (x_3 == 0)
{
lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_39 = lean_box(0);
lean_ctor_set(x_24, 0, x_39);
return x_24;
}
else
{
lean_free_object(x_24);
if (lean_obj_tag(x_2) == 0)
{
x_32 = x_4;
x_33 = x_5;
x_34 = x_28;
goto block_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_41 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(x_40, x_4, x_5, x_28);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_32 = x_4;
x_33 = x_5;
x_34 = x_42;
goto block_38;
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_4);
return x_41;
}
}
}
block_38:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(3, 1, 0);
} else {
 x_35 = x_31;
 lean_ctor_set_tag(x_35, 3);
}
lean_ctor_set(x_35, 0, x_30);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_36, x_32, x_33, x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_37;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_ctor_get(x_26, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_45 = x_26;
} else {
 lean_dec_ref(x_26);
 x_45 = lean_box(0);
}
if (x_3 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_43);
return x_54;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
x_46 = x_4;
x_47 = x_5;
x_48 = x_43;
goto block_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(x_55, x_4, x_5, x_43);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_46 = x_4;
x_47 = x_5;
x_48 = x_57;
goto block_52;
}
else
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_4);
return x_56;
}
}
}
block_52:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(3, 1, 0);
} else {
 x_49 = x_45;
 lean_ctor_set_tag(x_49, 3);
}
lean_ctor_set(x_49, 0, x_44);
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_50, x_46, x_47, x_48);
lean_dec(x_47);
lean_dec(x_46);
return x_51;
}
}
}
else
{
lean_dec(x_2);
if (x_3 == 0)
{
uint8_t x_58; 
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_24);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_24, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_24, 0, x_60);
return x_24;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_24, 1);
lean_inc(x_61);
lean_dec(x_24);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_24, 1);
lean_inc(x_64);
lean_dec(x_24);
x_65 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg(x_26, x_4, x_5, x_64);
lean_dec(x_5);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_4);
lean_dec(x_2);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_dec(x_24);
x_67 = lean_ctor_get(x_25, 0);
lean_inc(x_67);
lean_dec(x_25);
x_68 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_67, x_5, x_66);
lean_dec(x_5);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_24);
if (x_69 == 0)
{
return x_24;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_24, 0);
x_71 = lean_ctor_get(x_24, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_24);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_16);
lean_dec(x_2);
x_73 = lean_lcnf_compile_decls(x_1, x_4, x_5, x_10);
if (lean_obj_tag(x_73) == 0)
{
return x_73;
}
else
{
if (x_3 == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set_tag(x_73, 0);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
return x_73;
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_7, 0);
x_81 = lean_ctor_get(x_7, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_7);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Environment_constants(x_82);
x_84 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__0___boxed), 2, 1);
lean_closure_set(x_84, 0, x_83);
lean_inc(x_1);
x_85 = l_List_all___redArg(x_1, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_4, 2);
lean_inc(x_88);
x_89 = l_Lean_compiler_enableNew;
x_90 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc(x_1);
x_91 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__1___boxed), 5, 1);
lean_closure_set(x_91, 0, x_1);
x_92 = lean_alloc_closure((void*)(l_Lean_compileDecls_doCompile___lam__2___boxed), 5, 2);
lean_closure_set(x_92, 0, x_88);
lean_closure_set(x_92, 1, x_1);
x_93 = lean_mk_string_unchecked("compiler", 8, 8);
x_94 = l_Lean_Name_mkStr1(x_93);
x_95 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_5);
lean_inc(x_4);
x_96 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___redArg(x_94, x_91, x_92, x_85, x_95, x_4, x_5, x_81);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 12)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
if (x_3 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_110 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_100;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_99);
return x_111;
}
else
{
lean_dec(x_100);
if (lean_obj_tag(x_2) == 0)
{
x_103 = x_4;
x_104 = x_5;
x_105 = x_99;
goto block_109;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_2, 0);
lean_inc(x_112);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_113 = l___private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1(x_112, x_4, x_5, x_99);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_103 = x_4;
x_104 = x_5;
x_105 = x_114;
goto block_109;
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_5);
lean_dec(x_4);
return x_113;
}
}
}
block_109:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
if (lean_is_scalar(x_102)) {
 x_106 = lean_alloc_ctor(3, 1, 0);
} else {
 x_106 = x_102;
 lean_ctor_set_tag(x_106, 3);
}
lean_ctor_set(x_106, 0, x_101);
x_107 = l_Lean_MessageData_ofFormat(x_106);
x_108 = l_Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0___redArg(x_107, x_103, x_104, x_105);
lean_dec(x_104);
lean_dec(x_103);
return x_108;
}
}
else
{
lean_dec(x_2);
if (x_3 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_98);
lean_dec(x_5);
lean_dec(x_4);
x_115 = lean_ctor_get(x_96, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_116 = x_96;
} else {
 lean_dec_ref(x_96);
 x_116 = lean_box(0);
}
x_117 = lean_box(0);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_96, 1);
lean_inc(x_119);
lean_dec(x_96);
x_120 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg(x_98, x_4, x_5, x_119);
lean_dec(x_5);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_4);
lean_dec(x_2);
x_121 = lean_ctor_get(x_96, 1);
lean_inc(x_121);
lean_dec(x_96);
x_122 = lean_ctor_get(x_97, 0);
lean_inc(x_122);
lean_dec(x_97);
x_123 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_122, x_5, x_121);
lean_dec(x_5);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_124 = lean_ctor_get(x_96, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_96, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_126 = x_96;
} else {
 lean_dec_ref(x_96);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; 
lean_dec(x_88);
lean_dec(x_2);
x_128 = lean_lcnf_compile_decls(x_1, x_4, x_5, x_81);
if (lean_obj_tag(x_128) == 0)
{
return x_128;
}
else
{
if (x_3 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_box(0);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
 lean_ctor_set_tag(x_132, 0);
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
else
{
return x_128;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at___List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at___Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Declaration_foldExprM___at_____private_Lean_CoreM_0__Lean_checkUnsupported___at___Lean_compileDecls_doCompile_spec__1_spec__1___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at___Lean_compileDecls_doCompile_spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_compileDecls_doCompile___lam__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_compileDecls_doCompile___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_compileDecls_doCompile___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls_doCompile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_compileDecls_doCompile(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Environment_PromiseCheckedResult_commitChecked(x_2, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_9, x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_7);
x_12 = l_Lean_compileDecls_doCompile(x_2, x_3, x_4, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lean_compileDecls___lam__1(x_7, x_1, x_15, x_14);
lean_dec(x_15);
lean_dec(x_1);
lean_dec(x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = l_Lean_compileDecls___lam__1(x_7, x_1, x_23, x_22);
lean_dec(x_1);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_30 = lean_ctor_get(x_4, 2);
lean_inc(x_30);
x_31 = l_Lean_Elab_async;
x_32 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_dec(x_8);
goto block_29;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
lean_dec(x_8);
x_34 = l_Lean_Environment_isRealizing(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_35 = lean_st_ref_get(x_5, x_9);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_38);
x_39 = l_Lean_Environment_promiseChecked(x_38, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_42, x_5, x_41);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_IO_CancelToken_new(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(x_34);
x_49 = lean_alloc_closure((void*)(l_Lean_useDiagnosticMsg___lam__1___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_box(x_3);
x_51 = lean_alloc_closure((void*)(l_Lean_compileDecls___lam__0___boxed), 8, 4);
lean_closure_set(x_51, 0, x_40);
lean_closure_set(x_51, 1, x_1);
lean_closure_set(x_51, 2, x_2);
lean_closure_set(x_51, 3, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_46);
x_53 = lean_mk_string_unchecked("Lean", 4, 4);
x_54 = lean_mk_string_unchecked("compileDecls", 12, 12);
x_55 = l_Lean_Name_mkStr2(x_53, x_54);
x_56 = l_Lean_Name_toString(x_55, x_32, x_49);
lean_inc(x_4);
lean_inc(x_52);
x_57 = l_Lean_Core_wrapAsyncAsSnapshot___redArg(x_51, x_52, x_56, x_4, x_5, x_47);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_38, 2);
lean_inc(x_60);
lean_dec(x_38);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_io_map_task(x_58, x_60, x_61, x_34, x_59);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_71 = lean_ctor_get(x_4, 5);
lean_inc(x_71);
lean_dec(x_4);
x_72 = l_Lean_Syntax_getTailPos_x3f(x_71, x_34);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
lean_free_object(x_62);
x_73 = lean_box(0);
x_66 = x_73;
goto block_70;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_ctor_set(x_62, 1, x_75);
lean_ctor_set(x_62, 0, x_75);
lean_ctor_set(x_72, 0, x_62);
x_66 = x_72;
goto block_70;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec(x_72);
lean_inc(x_76);
lean_ctor_set(x_62, 1, x_76);
lean_ctor_set(x_62, 0, x_76);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_62);
x_66 = x_77;
goto block_70;
}
}
block_70:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_52);
lean_ctor_set(x_68, 3, x_64);
x_69 = l_Lean_Core_logSnapshotTask___redArg(x_68, x_5, x_65);
lean_dec(x_5);
return x_69;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_85; lean_object* x_86; 
x_78 = lean_ctor_get(x_62, 0);
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_62);
x_85 = lean_ctor_get(x_4, 5);
lean_inc(x_85);
lean_dec(x_4);
x_86 = l_Lean_Syntax_getTailPos_x3f(x_85, x_34);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_box(0);
x_80 = x_87;
goto block_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
lean_inc(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
x_80 = x_91;
goto block_84;
}
block_84:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_52);
lean_ctor_set(x_82, 3, x_78);
x_83 = l_Lean_Core_logSnapshotTask___redArg(x_82, x_5, x_79);
lean_dec(x_5);
return x_83;
}
}
}
else
{
goto block_29;
}
}
block_29:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_mk_string_unchecked("compiler env", 12, 12);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_traceBlock___redArg(x_14, x_15, x_4, x_5, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_compileDecls_doCompile(x_1, x_2, x_3, x_4, x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
return x_18;
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_compileDecls___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_compileDecls___lam__0(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_compileDecls(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = l_Lean_Compiler_getDeclNamesForCodeGen(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lean_compileDecls(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_compileDecl(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_getDiag(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_diagnostics;
x_3 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getDiag___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getDiag(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*13);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isDiagnosticsEnabled___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_isDiagnosticsEnabled___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isDiagnosticsEnabled___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isDiagnosticsEnabled(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_4 = lean_mk_string_unchecked("_uniq", 5, 5);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_unsigned_to_nat(5u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_nat_pow(x_5, x_8);
lean_dec(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_mk_empty_array_with_capacity(x_11);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_io_get_num_heartbeats(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Name_mkStr1(x_4);
x_24 = lean_uint64_of_nat(x_21);
lean_inc(x_12);
x_25 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set_usize(x_25, 4, x_7);
lean_inc(x_14);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_14);
lean_inc(x_12);
x_27 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set_usize(x_27, 4, x_7);
x_28 = lean_box(0);
x_29 = lean_box(1);
lean_inc(x_14);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_14);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_14);
x_32 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_12);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_21);
lean_ctor_set_usize(x_32, 4, x_7);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_ctor_set(x_17, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
x_34 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set_uint64(x_34, sizeof(void*)*1, x_24);
lean_inc(x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_26);
lean_inc(x_27);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_36, 2, x_28);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_32);
x_38 = lean_unbox(x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_38);
x_39 = lean_mk_empty_array_with_capacity(x_21);
lean_inc(x_35);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_5);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_36);
lean_ctor_set(x_40, 6, x_37);
lean_ctor_set(x_40, 7, x_39);
x_41 = lean_st_mk_ref(x_40, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_119 = l_Lean_inheritedTraceOptions;
x_120 = lean_st_ref_get(x_119, x_43);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_st_ref_get(x_42, x_122);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_168; uint8_t x_169; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
x_127 = lean_mk_string_unchecked("", 0, 0);
x_128 = l_Array_empty(lean_box(0));
x_129 = lean_mk_string_unchecked("<ImportM>", 9, 9);
lean_ctor_set(x_123, 1, x_128);
lean_ctor_set(x_123, 0, x_127);
x_130 = lean_box(0);
x_131 = lean_box(0);
x_132 = lean_box(0);
x_133 = lean_box(0);
x_134 = l_Lean_Core_getMaxHeartbeats(x_130);
x_135 = lean_box(0);
x_136 = lean_box(0);
x_137 = l_Lean_diagnostics;
x_138 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_130, x_137);
x_168 = lean_ctor_get(x_125, 0);
lean_inc(x_168);
lean_dec(x_125);
x_169 = l_Lean_Kernel_isDiagnosticsEnabled(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
if (x_138 == 0)
{
lean_inc(x_42);
x_139 = x_42;
x_140 = x_126;
goto block_152;
}
else
{
goto block_167;
}
}
else
{
if (x_138 == 0)
{
goto block_167;
}
else
{
lean_inc(x_42);
x_139 = x_42;
x_140 = x_126;
goto block_152;
}
}
block_152:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; uint8_t x_151; 
x_141 = lean_st_ref_get(x_139, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_maxRecDepth;
x_145 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_130, x_144);
x_146 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_146, 0, x_129);
lean_ctor_set(x_146, 1, x_123);
lean_ctor_set(x_146, 2, x_130);
lean_ctor_set(x_146, 3, x_21);
lean_ctor_set(x_146, 4, x_145);
lean_ctor_set(x_146, 5, x_131);
lean_ctor_set(x_146, 6, x_132);
lean_ctor_set(x_146, 7, x_133);
lean_ctor_set(x_146, 8, x_19);
lean_ctor_set(x_146, 9, x_134);
lean_ctor_set(x_146, 10, x_22);
lean_ctor_set(x_146, 11, x_136);
lean_ctor_set(x_146, 12, x_121);
lean_ctor_set_uint8(x_146, sizeof(void*)*13, x_138);
x_147 = lean_unbox(x_135);
lean_ctor_set_uint8(x_146, sizeof(void*)*13 + 1, x_147);
x_148 = lean_ctor_get(x_2, 1);
lean_inc(x_148);
lean_dec(x_2);
x_149 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_148, x_137);
x_150 = lean_ctor_get(x_142, 0);
lean_inc(x_150);
lean_dec(x_142);
x_151 = l_Lean_Kernel_isDiagnosticsEnabled(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
if (x_149 == 0)
{
lean_dec(x_35);
x_44 = x_144;
x_45 = x_148;
x_46 = x_149;
x_47 = x_146;
x_48 = x_139;
x_49 = x_143;
goto block_97;
}
else
{
x_98 = x_139;
x_99 = x_143;
x_100 = x_144;
x_101 = x_148;
x_102 = x_146;
x_103 = x_149;
goto block_118;
}
}
else
{
if (x_149 == 0)
{
x_98 = x_139;
x_99 = x_143;
x_100 = x_144;
x_101 = x_148;
x_102 = x_146;
x_103 = x_149;
goto block_118;
}
else
{
lean_dec(x_35);
x_44 = x_144;
x_45 = x_148;
x_46 = x_149;
x_47 = x_146;
x_48 = x_139;
x_49 = x_143;
goto block_97;
}
}
}
block_167:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_153 = lean_st_ref_take(x_42, x_126);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = l_Lean_Kernel_enableDiag(x_156, x_138);
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_154, 5);
lean_inc(x_161);
x_162 = lean_ctor_get(x_154, 6);
lean_inc(x_162);
x_163 = lean_ctor_get(x_154, 7);
lean_inc(x_163);
lean_dec(x_154);
lean_inc(x_35);
x_164 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set(x_164, 4, x_35);
lean_ctor_set(x_164, 5, x_161);
lean_ctor_set(x_164, 6, x_162);
lean_ctor_set(x_164, 7, x_163);
x_165 = lean_st_ref_set(x_42, x_164, x_155);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
lean_inc(x_42);
x_139 = x_42;
x_140 = x_166;
goto block_152;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_214; uint8_t x_215; 
x_170 = lean_ctor_get(x_123, 0);
x_171 = lean_ctor_get(x_123, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_123);
x_172 = lean_mk_string_unchecked("", 0, 0);
x_173 = l_Array_empty(lean_box(0));
x_174 = lean_mk_string_unchecked("<ImportM>", 9, 9);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
x_176 = lean_box(0);
x_177 = lean_box(0);
x_178 = lean_box(0);
x_179 = lean_box(0);
x_180 = l_Lean_Core_getMaxHeartbeats(x_176);
x_181 = lean_box(0);
x_182 = lean_box(0);
x_183 = l_Lean_diagnostics;
x_184 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_176, x_183);
x_214 = lean_ctor_get(x_170, 0);
lean_inc(x_214);
lean_dec(x_170);
x_215 = l_Lean_Kernel_isDiagnosticsEnabled(x_214);
lean_dec(x_214);
if (x_215 == 0)
{
if (x_184 == 0)
{
lean_inc(x_42);
x_185 = x_42;
x_186 = x_171;
goto block_198;
}
else
{
goto block_213;
}
}
else
{
if (x_184 == 0)
{
goto block_213;
}
else
{
lean_inc(x_42);
x_185 = x_42;
x_186 = x_171;
goto block_198;
}
}
block_198:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; uint8_t x_197; 
x_187 = lean_st_ref_get(x_185, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_maxRecDepth;
x_191 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_176, x_190);
x_192 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_192, 0, x_174);
lean_ctor_set(x_192, 1, x_175);
lean_ctor_set(x_192, 2, x_176);
lean_ctor_set(x_192, 3, x_21);
lean_ctor_set(x_192, 4, x_191);
lean_ctor_set(x_192, 5, x_177);
lean_ctor_set(x_192, 6, x_178);
lean_ctor_set(x_192, 7, x_179);
lean_ctor_set(x_192, 8, x_19);
lean_ctor_set(x_192, 9, x_180);
lean_ctor_set(x_192, 10, x_22);
lean_ctor_set(x_192, 11, x_182);
lean_ctor_set(x_192, 12, x_121);
lean_ctor_set_uint8(x_192, sizeof(void*)*13, x_184);
x_193 = lean_unbox(x_181);
lean_ctor_set_uint8(x_192, sizeof(void*)*13 + 1, x_193);
x_194 = lean_ctor_get(x_2, 1);
lean_inc(x_194);
lean_dec(x_2);
x_195 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_194, x_183);
x_196 = lean_ctor_get(x_188, 0);
lean_inc(x_196);
lean_dec(x_188);
x_197 = l_Lean_Kernel_isDiagnosticsEnabled(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
if (x_195 == 0)
{
lean_dec(x_35);
x_44 = x_190;
x_45 = x_194;
x_46 = x_195;
x_47 = x_192;
x_48 = x_185;
x_49 = x_189;
goto block_97;
}
else
{
x_98 = x_185;
x_99 = x_189;
x_100 = x_190;
x_101 = x_194;
x_102 = x_192;
x_103 = x_195;
goto block_118;
}
}
else
{
if (x_195 == 0)
{
x_98 = x_185;
x_99 = x_189;
x_100 = x_190;
x_101 = x_194;
x_102 = x_192;
x_103 = x_195;
goto block_118;
}
else
{
lean_dec(x_35);
x_44 = x_190;
x_45 = x_194;
x_46 = x_195;
x_47 = x_192;
x_48 = x_185;
x_49 = x_189;
goto block_97;
}
}
}
block_213:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_199 = lean_st_ref_take(x_42, x_171);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
x_203 = l_Lean_Kernel_enableDiag(x_202, x_184);
x_204 = lean_ctor_get(x_200, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 5);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 6);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 7);
lean_inc(x_209);
lean_dec(x_200);
lean_inc(x_35);
x_210 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_206);
lean_ctor_set(x_210, 4, x_35);
lean_ctor_set(x_210, 5, x_207);
lean_ctor_set(x_210, 6, x_208);
lean_ctor_set(x_210, 7, x_209);
x_211 = lean_st_ref_set(x_42, x_210, x_201);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
lean_inc(x_42);
x_185 = x_42;
x_186 = x_212;
goto block_198;
}
}
block_97:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 3);
lean_inc(x_52);
x_53 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_45, x_44);
lean_dec(x_44);
x_54 = lean_ctor_get(x_47, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_47, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_47, 7);
lean_inc(x_56);
x_57 = lean_ctor_get(x_47, 8);
lean_inc(x_57);
x_58 = lean_ctor_get(x_47, 9);
lean_inc(x_58);
x_59 = lean_ctor_get(x_47, 10);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 11);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_47, sizeof(void*)*13 + 1);
x_62 = lean_ctor_get(x_47, 12);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_51);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_52);
lean_ctor_set(x_63, 4, x_53);
lean_ctor_set(x_63, 5, x_54);
lean_ctor_set(x_63, 6, x_55);
lean_ctor_set(x_63, 7, x_56);
lean_ctor_set(x_63, 8, x_57);
lean_ctor_set(x_63, 9, x_58);
lean_ctor_set(x_63, 10, x_59);
lean_ctor_set(x_63, 11, x_60);
lean_ctor_set(x_63, 12, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*13, x_46);
lean_ctor_set_uint8(x_63, sizeof(void*)*13 + 1, x_61);
x_64 = lean_apply_3(x_1, x_63, x_48, x_49);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_42, x_66);
lean_dec(x_42);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_42);
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_64, 1);
lean_inc(x_73);
lean_dec(x_64);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_MessageData_toString(x_74, x_73);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_81, 0, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_64);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_64, 0);
lean_dec(x_84);
x_85 = lean_ctor_get(x_72, 0);
lean_inc(x_85);
lean_dec(x_72);
x_86 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_87 = l___private_Init_Data_Repr_0__Nat_reprFast(x_85);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
x_89 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_64, 0, x_89);
return x_64;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_64, 1);
lean_inc(x_90);
lean_dec(x_64);
x_91 = lean_ctor_get(x_72, 0);
lean_inc(x_91);
lean_dec(x_72);
x_92 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_93 = l___private_Init_Data_Repr_0__Nat_reprFast(x_91);
x_94 = lean_string_append(x_92, x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
return x_96;
}
}
}
}
block_118:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_104 = lean_st_ref_take(x_98, x_99);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = l_Lean_Kernel_enableDiag(x_107, x_103);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_105, 5);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 6);
lean_inc(x_113);
x_114 = lean_ctor_get(x_105, 7);
lean_inc(x_114);
lean_dec(x_105);
x_115 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_111);
lean_ctor_set(x_115, 4, x_35);
lean_ctor_set(x_115, 5, x_112);
lean_ctor_set(x_115, 6, x_113);
lean_ctor_set(x_115, 7, x_114);
x_116 = lean_st_ref_set(x_98, x_115, x_106);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_44 = x_100;
x_45 = x_101;
x_46 = x_103;
x_47 = x_102;
x_48 = x_98;
x_49 = x_117;
goto block_97;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint64_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_358; uint8_t x_359; 
x_216 = lean_ctor_get(x_17, 0);
x_217 = lean_ctor_get(x_17, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_17);
x_218 = lean_unsigned_to_nat(0u);
x_219 = lean_unsigned_to_nat(1u);
x_220 = l_Lean_Name_mkStr1(x_4);
x_221 = lean_uint64_of_nat(x_218);
lean_inc(x_12);
x_222 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_222, 0, x_13);
lean_ctor_set(x_222, 1, x_12);
lean_ctor_set(x_222, 2, x_218);
lean_ctor_set(x_222, 3, x_218);
lean_ctor_set_usize(x_222, 4, x_7);
lean_inc(x_14);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_14);
lean_inc(x_12);
x_224 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_224, 0, x_15);
lean_ctor_set(x_224, 1, x_12);
lean_ctor_set(x_224, 2, x_218);
lean_ctor_set(x_224, 3, x_218);
lean_ctor_set_usize(x_224, 4, x_7);
x_225 = lean_box(0);
x_226 = lean_box(1);
lean_inc(x_14);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_14);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_14);
x_229 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_229, 0, x_16);
lean_ctor_set(x_229, 1, x_12);
lean_ctor_set(x_229, 2, x_218);
lean_ctor_set(x_229, 3, x_218);
lean_ctor_set_usize(x_229, 4, x_7);
x_230 = lean_ctor_get(x_2, 0);
lean_inc(x_230);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_220);
lean_ctor_set(x_231, 1, x_219);
x_232 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_232, 0, x_222);
lean_ctor_set_uint64(x_232, sizeof(void*)*1, x_221);
lean_inc(x_223);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_223);
lean_ctor_set(x_233, 1, x_223);
lean_inc(x_224);
x_234 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_234, 0, x_224);
lean_ctor_set(x_234, 1, x_224);
lean_ctor_set(x_234, 2, x_225);
x_235 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_235, 0, x_227);
lean_ctor_set(x_235, 1, x_228);
lean_ctor_set(x_235, 2, x_229);
x_236 = lean_unbox(x_226);
lean_ctor_set_uint8(x_235, sizeof(void*)*3, x_236);
x_237 = lean_mk_empty_array_with_capacity(x_218);
lean_inc(x_233);
x_238 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_238, 0, x_230);
lean_ctor_set(x_238, 1, x_5);
lean_ctor_set(x_238, 2, x_231);
lean_ctor_set(x_238, 3, x_232);
lean_ctor_set(x_238, 4, x_233);
lean_ctor_set(x_238, 5, x_234);
lean_ctor_set(x_238, 6, x_235);
lean_ctor_set(x_238, 7, x_237);
x_239 = lean_st_mk_ref(x_238, x_217);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_308 = l_Lean_inheritedTraceOptions;
x_309 = lean_st_ref_get(x_308, x_241);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_st_ref_get(x_240, x_311);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_315 = x_312;
} else {
 lean_dec_ref(x_312);
 x_315 = lean_box(0);
}
x_316 = lean_mk_string_unchecked("", 0, 0);
x_317 = l_Array_empty(lean_box(0));
x_318 = lean_mk_string_unchecked("<ImportM>", 9, 9);
if (lean_is_scalar(x_315)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_315;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
x_320 = lean_box(0);
x_321 = lean_box(0);
x_322 = lean_box(0);
x_323 = lean_box(0);
x_324 = l_Lean_Core_getMaxHeartbeats(x_320);
x_325 = lean_box(0);
x_326 = lean_box(0);
x_327 = l_Lean_diagnostics;
x_328 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_320, x_327);
x_358 = lean_ctor_get(x_313, 0);
lean_inc(x_358);
lean_dec(x_313);
x_359 = l_Lean_Kernel_isDiagnosticsEnabled(x_358);
lean_dec(x_358);
if (x_359 == 0)
{
if (x_328 == 0)
{
lean_inc(x_240);
x_329 = x_240;
x_330 = x_314;
goto block_342;
}
else
{
goto block_357;
}
}
else
{
if (x_328 == 0)
{
goto block_357;
}
else
{
lean_inc(x_240);
x_329 = x_240;
x_330 = x_314;
goto block_342;
}
}
block_286:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_245, 3);
lean_inc(x_250);
x_251 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_243, x_242);
lean_dec(x_242);
x_252 = lean_ctor_get(x_245, 5);
lean_inc(x_252);
x_253 = lean_ctor_get(x_245, 6);
lean_inc(x_253);
x_254 = lean_ctor_get(x_245, 7);
lean_inc(x_254);
x_255 = lean_ctor_get(x_245, 8);
lean_inc(x_255);
x_256 = lean_ctor_get(x_245, 9);
lean_inc(x_256);
x_257 = lean_ctor_get(x_245, 10);
lean_inc(x_257);
x_258 = lean_ctor_get(x_245, 11);
lean_inc(x_258);
x_259 = lean_ctor_get_uint8(x_245, sizeof(void*)*13 + 1);
x_260 = lean_ctor_get(x_245, 12);
lean_inc(x_260);
lean_dec(x_245);
x_261 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_261, 0, x_248);
lean_ctor_set(x_261, 1, x_249);
lean_ctor_set(x_261, 2, x_243);
lean_ctor_set(x_261, 3, x_250);
lean_ctor_set(x_261, 4, x_251);
lean_ctor_set(x_261, 5, x_252);
lean_ctor_set(x_261, 6, x_253);
lean_ctor_set(x_261, 7, x_254);
lean_ctor_set(x_261, 8, x_255);
lean_ctor_set(x_261, 9, x_256);
lean_ctor_set(x_261, 10, x_257);
lean_ctor_set(x_261, 11, x_258);
lean_ctor_set(x_261, 12, x_260);
lean_ctor_set_uint8(x_261, sizeof(void*)*13, x_244);
lean_ctor_set_uint8(x_261, sizeof(void*)*13 + 1, x_259);
x_262 = lean_apply_3(x_1, x_261, x_246, x_247);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_st_ref_get(x_240, x_264);
lean_dec(x_240);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_263);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
else
{
lean_object* x_269; 
lean_dec(x_240);
x_269 = lean_ctor_get(x_262, 0);
lean_inc(x_269);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_270 = lean_ctor_get(x_262, 1);
lean_inc(x_270);
lean_dec(x_262);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = l_Lean_MessageData_toString(x_271, x_270);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_276, 0, x_273);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_275;
 lean_ctor_set_tag(x_277, 1);
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_274);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_278 = lean_ctor_get(x_262, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_279 = x_262;
} else {
 lean_dec_ref(x_262);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_269, 0);
lean_inc(x_280);
lean_dec(x_269);
x_281 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_282 = l___private_Init_Data_Repr_0__Nat_reprFast(x_280);
x_283 = lean_string_append(x_281, x_282);
lean_dec(x_282);
x_284 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_284, 0, x_283);
if (lean_is_scalar(x_279)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_279;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_278);
return x_285;
}
}
}
block_307:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_293 = lean_st_ref_take(x_287, x_288);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_ctor_get(x_294, 0);
lean_inc(x_296);
x_297 = l_Lean_Kernel_enableDiag(x_296, x_292);
x_298 = lean_ctor_get(x_294, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_294, 2);
lean_inc(x_299);
x_300 = lean_ctor_get(x_294, 3);
lean_inc(x_300);
x_301 = lean_ctor_get(x_294, 5);
lean_inc(x_301);
x_302 = lean_ctor_get(x_294, 6);
lean_inc(x_302);
x_303 = lean_ctor_get(x_294, 7);
lean_inc(x_303);
lean_dec(x_294);
x_304 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_304, 0, x_297);
lean_ctor_set(x_304, 1, x_298);
lean_ctor_set(x_304, 2, x_299);
lean_ctor_set(x_304, 3, x_300);
lean_ctor_set(x_304, 4, x_233);
lean_ctor_set(x_304, 5, x_301);
lean_ctor_set(x_304, 6, x_302);
lean_ctor_set(x_304, 7, x_303);
x_305 = lean_st_ref_set(x_287, x_304, x_295);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_242 = x_289;
x_243 = x_290;
x_244 = x_292;
x_245 = x_291;
x_246 = x_287;
x_247 = x_306;
goto block_286;
}
block_342:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; uint8_t x_341; 
x_331 = lean_st_ref_get(x_329, x_330);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = l_Lean_maxRecDepth;
x_335 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_320, x_334);
x_336 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_336, 0, x_318);
lean_ctor_set(x_336, 1, x_319);
lean_ctor_set(x_336, 2, x_320);
lean_ctor_set(x_336, 3, x_218);
lean_ctor_set(x_336, 4, x_335);
lean_ctor_set(x_336, 5, x_321);
lean_ctor_set(x_336, 6, x_322);
lean_ctor_set(x_336, 7, x_323);
lean_ctor_set(x_336, 8, x_216);
lean_ctor_set(x_336, 9, x_324);
lean_ctor_set(x_336, 10, x_219);
lean_ctor_set(x_336, 11, x_326);
lean_ctor_set(x_336, 12, x_310);
lean_ctor_set_uint8(x_336, sizeof(void*)*13, x_328);
x_337 = lean_unbox(x_325);
lean_ctor_set_uint8(x_336, sizeof(void*)*13 + 1, x_337);
x_338 = lean_ctor_get(x_2, 1);
lean_inc(x_338);
lean_dec(x_2);
x_339 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_338, x_327);
x_340 = lean_ctor_get(x_332, 0);
lean_inc(x_340);
lean_dec(x_332);
x_341 = l_Lean_Kernel_isDiagnosticsEnabled(x_340);
lean_dec(x_340);
if (x_341 == 0)
{
if (x_339 == 0)
{
lean_dec(x_233);
x_242 = x_334;
x_243 = x_338;
x_244 = x_339;
x_245 = x_336;
x_246 = x_329;
x_247 = x_333;
goto block_286;
}
else
{
x_287 = x_329;
x_288 = x_333;
x_289 = x_334;
x_290 = x_338;
x_291 = x_336;
x_292 = x_339;
goto block_307;
}
}
else
{
if (x_339 == 0)
{
x_287 = x_329;
x_288 = x_333;
x_289 = x_334;
x_290 = x_338;
x_291 = x_336;
x_292 = x_339;
goto block_307;
}
else
{
lean_dec(x_233);
x_242 = x_334;
x_243 = x_338;
x_244 = x_339;
x_245 = x_336;
x_246 = x_329;
x_247 = x_333;
goto block_286;
}
}
}
block_357:
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_343 = lean_st_ref_take(x_240, x_314);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
x_347 = l_Lean_Kernel_enableDiag(x_346, x_328);
x_348 = lean_ctor_get(x_344, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_344, 2);
lean_inc(x_349);
x_350 = lean_ctor_get(x_344, 3);
lean_inc(x_350);
x_351 = lean_ctor_get(x_344, 5);
lean_inc(x_351);
x_352 = lean_ctor_get(x_344, 6);
lean_inc(x_352);
x_353 = lean_ctor_get(x_344, 7);
lean_inc(x_353);
lean_dec(x_344);
lean_inc(x_233);
x_354 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_354, 0, x_347);
lean_ctor_set(x_354, 1, x_348);
lean_ctor_set(x_354, 2, x_349);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set(x_354, 4, x_233);
lean_ctor_set(x_354, 5, x_351);
lean_ctor_set(x_354, 6, x_352);
lean_ctor_set(x_354, 7, x_353);
x_355 = lean_st_ref_set(x_240, x_354, x_345);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec(x_355);
lean_inc(x_240);
x_329 = x_240;
x_330 = x_356;
goto block_342;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportM_runCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ImportM_runCoreM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isRuntime(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Exception_isMaxHeartbeat(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Exception_isMaxRecDepth(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isRuntime___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isRuntime(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_12 = l_Lean_Exception_isInterrupt(x_7);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isRuntime(x_7);
x_9 = x_13;
goto block_11;
}
else
{
x_9 = x_12;
goto block_11;
}
block_11:
{
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_apply_4(x_2, x_7, x_3, x_4, x_8);
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_13 = l_Lean_Exception_isInterrupt(x_8);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Exception_isRuntime(x_8);
x_10 = x_14;
goto block_12;
}
else
{
x_10 = x_13;
goto block_12;
}
block_12:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_apply_4(x_3, x_8, x_4, x_5, x_9);
return x_11;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Lean_Exception_isInterrupt(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_apply_4(x_2, x_7, x_3, x_4, x_8);
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_tryCatchRuntimeEx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = l_Lean_Exception_isInterrupt(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_apply_4(x_3, x_8, x_4, x_5, x_9);
return x_11;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instMonadExceptOfExceptionCoreM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Core_tryCatch), 6, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadExceptOfExceptionCoreM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_instMonadExceptOfExceptionCoreM___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instMonadRuntimeExceptionCoreM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_tryCatchRuntimeEx), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_apply_3(x_1, lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionReaderT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionReaderT___redArg___lam__1), 5, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_apply_3(x_1, lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRuntimeExceptionStateRefT_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_instMonadRuntimeExceptionStateRefT_x27___redArg___lam__1), 5, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_3, lean_box(0), x_1);
x_8 = lean_apply_5(x_2, lean_box(0), x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_alloc_closure((void*)(l_Lean_mapCoreM___redArg___lam__0), 6, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_9, lean_box(0));
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mapCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_alloc_closure((void*)(l_Lean_mapCoreM___redArg___lam__0), 6, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_apply_2(x_9, lean_box(0), x_7);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_1(x_11, lean_box(0));
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 5);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_NameSet_contains(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_4);
x_11 = lean_st_ref_take(x_2, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_NameSet_insert(x_22, x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_ctor_get(x_12, 6);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 7);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_17);
lean_ctor_set(x_27, 4, x_18);
lean_ctor_set(x_27, 5, x_24);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_13);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(1);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_4, 0, x_35);
return x_4;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_ctor_get(x_36, 5);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_NameSet_contains(x_39, x_1);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_41 = lean_st_ref_take(x_2, x_37);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 2);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_NameSet_insert(x_52, x_1);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_ctor_get(x_42, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 7);
lean_inc(x_56);
lean_dec(x_42);
x_57 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_45);
lean_ctor_set(x_57, 2, x_46);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_54);
lean_ctor_set(x_57, 6, x_55);
lean_ctor_set(x_57, 7, x_56);
x_58 = lean_st_ref_set(x_2, x_57, x_43);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(1);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_37);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logMessageKind___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_logMessageKind___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logMessageKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logMessageKind(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Environment_enableRealizationsForConst(x_8, x_9, x_1, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_11, x_3, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_enableRealizationsForConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_enableRealizationsForConst(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_CoreM___hyg_6713_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("async", 5, 5);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("initFn", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("_@", 2, 2);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = l_Lean_Name_str___override(x_12, x_7);
x_14 = lean_mk_string_unchecked("CoreM", 5, 5);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("_hyg", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_unsigned_to_nat(6713u);
x_19 = l_Lean_Name_num___override(x_17, x_18);
x_20 = lean_unbox(x_5);
lean_inc(x_19);
x_21 = l_Lean_registerTraceClass(x_4, x_20, x_19, x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("block", 5, 5);
x_24 = l_Lean_Name_mkStr2(x_2, x_23);
x_25 = lean_unbox(x_5);
x_26 = l_Lean_registerTraceClass(x_24, x_25, x_19, x_22);
return x_26;
}
else
{
lean_dec(x_19);
lean_dec(x_2);
return x_21;
}
}
}
lean_object* initialize_Lean_Util_RecDepth(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Language_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_RecDepth(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_40_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_diagnostics_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_diagnostics_threshold);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_80_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_maxHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_maxHeartbeats);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_114_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_async = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_async);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_153_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_inServer = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_inServer);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_192_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_internal_cmdlineSnapshots = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_internal_cmdlineSnapshots);
lean_dec_ref(res);
}l_Lean_useDiagnosticMsg = _init_l_Lean_useDiagnosticMsg();
lean_mark_persistent(l_Lean_useDiagnosticMsg);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_263_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Core_instInhabitedCache = _init_l_Lean_Core_instInhabitedCache();
lean_mark_persistent(l_Lean_Core_instInhabitedCache);
l_Lean_Core_instMonadCoreM = _init_l_Lean_Core_instMonadCoreM();
lean_mark_persistent(l_Lean_Core_instMonadCoreM);
l_Lean_Core_instMonadRefCoreM = _init_l_Lean_Core_instMonadRefCoreM();
lean_mark_persistent(l_Lean_Core_instMonadRefCoreM);
l_Lean_Core_instMonadEnvCoreM = _init_l_Lean_Core_instMonadEnvCoreM();
lean_mark_persistent(l_Lean_Core_instMonadEnvCoreM);
l_Lean_Core_instMonadOptionsCoreM = _init_l_Lean_Core_instMonadOptionsCoreM();
lean_mark_persistent(l_Lean_Core_instMonadOptionsCoreM);
l_Lean_Core_instMonadWithOptionsCoreM = _init_l_Lean_Core_instMonadWithOptionsCoreM();
lean_mark_persistent(l_Lean_Core_instMonadWithOptionsCoreM);
l_Lean_Core_instAddMessageContextCoreM = _init_l_Lean_Core_instAddMessageContextCoreM();
lean_mark_persistent(l_Lean_Core_instAddMessageContextCoreM);
l_Lean_Core_instMonadNameGeneratorCoreM = _init_l_Lean_Core_instMonadNameGeneratorCoreM();
lean_mark_persistent(l_Lean_Core_instMonadNameGeneratorCoreM);
l_Lean_Core_instMonadRecDepthCoreM = _init_l_Lean_Core_instMonadRecDepthCoreM();
lean_mark_persistent(l_Lean_Core_instMonadRecDepthCoreM);
l_Lean_Core_instMonadResolveNameCoreM = _init_l_Lean_Core_instMonadResolveNameCoreM();
lean_mark_persistent(l_Lean_Core_instMonadResolveNameCoreM);
l_Lean_Core_instMonadQuotationCoreM = _init_l_Lean_Core_instMonadQuotationCoreM();
lean_mark_persistent(l_Lean_Core_instMonadQuotationCoreM);
l_Lean_Core_instMonadInfoTreeCoreM = _init_l_Lean_Core_instMonadInfoTreeCoreM();
lean_mark_persistent(l_Lean_Core_instMonadInfoTreeCoreM);
l_Lean_Core_instMonadLiftIOCoreM = _init_l_Lean_Core_instMonadLiftIOCoreM();
lean_mark_persistent(l_Lean_Core_instMonadLiftIOCoreM);
l_Lean_Core_instMonadTraceCoreM = _init_l_Lean_Core_instMonadTraceCoreM();
lean_mark_persistent(l_Lean_Core_instMonadTraceCoreM);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_2986_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_debug_moduleNameAtTimeout = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_debug_moduleNameAtTimeout);
lean_dec_ref(res);
}l_Lean_Core_instMonadLogCoreM = _init_l_Lean_Core_instMonadLogCoreM();
lean_mark_persistent(l_Lean_Core_instMonadLogCoreM);
if (builtin) {res = l_Lean_Core_initFn____x40_Lean_CoreM___hyg_3937_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Core_stderrAsMessages = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Core_stderrAsMessages);
lean_dec_ref(res);
}l___auto____x40_Lean_CoreM___hyg_3975_ = _init_l___auto____x40_Lean_CoreM___hyg_3975_();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_3975_);
l___auto____x40_Lean_CoreM___hyg_4116_ = _init_l___auto____x40_Lean_CoreM___hyg_4116_();
lean_mark_persistent(l___auto____x40_Lean_CoreM___hyg_4116_);
l___private_Lean_CoreM_0__Lean_supportedRecursors = _init_l___private_Lean_CoreM_0__Lean_supportedRecursors();
lean_mark_persistent(l___private_Lean_CoreM_0__Lean_supportedRecursors);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_5018_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_compiler_enableNew = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_compiler_enableNew);
lean_dec_ref(res);
}l_Lean_instMonadExceptOfExceptionCoreM = _init_l_Lean_instMonadExceptOfExceptionCoreM();
lean_mark_persistent(l_Lean_instMonadExceptOfExceptionCoreM);
l_Lean_instMonadRuntimeExceptionCoreM = _init_l_Lean_instMonadRuntimeExceptionCoreM();
lean_mark_persistent(l_Lean_instMonadRuntimeExceptionCoreM);
if (builtin) {res = l_Lean_initFn____x40_Lean_CoreM___hyg_6713_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
