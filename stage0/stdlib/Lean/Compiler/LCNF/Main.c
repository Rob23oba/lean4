// Lean compiler output
// Module: Lean.Compiler.LCNF.Main
// Imports: Lean.Compiler.Options Lean.Compiler.ExternAttr Lean.Compiler.IR Lean.Compiler.IR.Basic Lean.Compiler.IR.Checker Lean.Compiler.IR.ToIR Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.Passes Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.ToDecl Lean.Compiler.LCNF.Check Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.CSE
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LogEntry_fmt(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_hasMacroInlineAttribute(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Decl_save_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_get_implemented_by(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_lcnf_compile_decls(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1699_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_markRecDecls(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_check;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__1(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_ir_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
extern lean_object* l_Lean_compiler_enableNew;
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_11 = l_Lean_Meta_isProp(x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_isTypeFormerType(x_10, x_2, x_3, x_4, x_5, x_14);
return x_15;
}
else
{
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_is_matcher(x_7, x_1);
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
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_is_matcher(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_shouldGenerateCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_59; lean_object* x_60; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint64_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; lean_object* x_143; 
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_unsigned_to_nat(5u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_nat_pow(x_7, x_10);
lean_dec(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_6);
lean_inc(x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_6);
lean_inc(x_6);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
lean_inc(x_6);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_6);
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_6);
lean_inc(x_6);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_6);
lean_inc(x_17);
x_23 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
lean_ctor_set(x_23, 8, x_22);
lean_inc(x_6);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_6);
lean_inc(x_6);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_6);
lean_inc(x_6);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_6);
lean_inc(x_6);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_6);
lean_inc(x_27);
lean_inc(x_24);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_27);
lean_inc(x_14);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_14);
lean_inc(x_14);
x_30 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
lean_ctor_set(x_30, 2, x_16);
lean_ctor_set(x_30, 3, x_16);
lean_ctor_set_usize(x_30, 4, x_9);
lean_inc(x_6);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_6);
lean_inc_n(x_17, 2);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_17);
lean_ctor_set(x_32, 2, x_17);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_5);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_mk_ref(x_33, x_4);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
x_39 = lean_box(1);
x_110 = lean_box(1);
x_111 = lean_box(0);
x_112 = lean_box(2);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_6);
x_114 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_114, 0, x_15);
lean_ctor_set(x_114, 1, x_14);
lean_ctor_set(x_114, 2, x_16);
lean_ctor_set(x_114, 3, x_16);
lean_ctor_set_usize(x_114, 4, x_9);
x_115 = lean_alloc_ctor(0, 0, 18);
x_116 = lean_unbox(x_38);
lean_ctor_set_uint8(x_115, 0, x_116);
x_117 = lean_unbox(x_38);
lean_ctor_set_uint8(x_115, 1, x_117);
x_118 = lean_unbox(x_38);
lean_ctor_set_uint8(x_115, 2, x_118);
x_119 = lean_unbox(x_38);
lean_ctor_set_uint8(x_115, 3, x_119);
x_120 = lean_unbox(x_38);
lean_ctor_set_uint8(x_115, 4, x_120);
x_121 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 5, x_121);
x_122 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 6, x_122);
x_123 = lean_unbox(x_38);
lean_ctor_set_uint8(x_115, 7, x_123);
x_124 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 8, x_124);
x_125 = lean_unbox(x_110);
lean_ctor_set_uint8(x_115, 9, x_125);
x_126 = lean_unbox(x_111);
lean_ctor_set_uint8(x_115, 10, x_126);
x_127 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 11, x_127);
x_128 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 12, x_128);
x_129 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 13, x_129);
x_130 = lean_unbox(x_112);
lean_ctor_set_uint8(x_115, 14, x_130);
x_131 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 15, x_131);
x_132 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 16, x_132);
x_133 = lean_unbox(x_39);
lean_ctor_set_uint8(x_115, 17, x_133);
x_134 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_115);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_113);
lean_ctor_set(x_135, 1, x_114);
lean_ctor_set(x_135, 2, x_5);
x_136 = lean_mk_empty_array_with_capacity(x_16);
x_137 = lean_box(0);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_139, 0, x_115);
lean_ctor_set(x_139, 1, x_5);
lean_ctor_set(x_139, 2, x_135);
lean_ctor_set(x_139, 3, x_136);
lean_ctor_set(x_139, 4, x_137);
lean_ctor_set(x_139, 5, x_16);
lean_ctor_set(x_139, 6, x_138);
lean_ctor_set_uint64(x_139, sizeof(void*)*7, x_134);
x_140 = lean_unbox(x_38);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 8, x_140);
x_141 = lean_unbox(x_38);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 9, x_141);
x_142 = lean_unbox(x_38);
lean_ctor_set_uint8(x_139, sizeof(void*)*7 + 10, x_142);
lean_inc(x_3);
lean_inc(x_35);
lean_inc(x_1);
x_143 = l_Lean_Compiler_LCNF_shouldGenerateCode_isCompIrrelevant(x_1, x_139, x_35, x_2, x_3, x_36);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_st_ref_get(x_35, x_145);
lean_dec(x_35);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = lean_unbox(x_144);
lean_dec(x_144);
x_59 = x_148;
x_60 = x_147;
goto block_109;
}
else
{
lean_dec(x_35);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_143, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_dec(x_143);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_59 = x_151;
x_60 = x_150;
goto block_109;
}
else
{
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
return x_143;
}
}
block_58:
{
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_37);
lean_inc(x_1);
x_43 = l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(x_1, x_3, x_41);
lean_dec(x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
x_48 = l_Lean_isCasesOnRecursor(x_40, x_1);
if (x_48 == 0)
{
lean_ctor_set(x_43, 0, x_39);
return x_43;
}
else
{
lean_ctor_set(x_43, 0, x_38);
return x_43;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = l_Lean_isCasesOnRecursor(x_40, x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_40);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_43, 0);
lean_dec(x_54);
lean_ctor_set(x_43, 0, x_38);
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_dec(x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_37)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_37;
}
lean_ctor_set(x_57, 0, x_38);
lean_ctor_set(x_57, 1, x_41);
return x_57;
}
}
block_109:
{
if (x_59 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_st_ref_get(x_3, x_60);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_1);
lean_inc(x_65);
x_66 = l_Lean_isExtern(x_65, x_1);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_free_object(x_61);
lean_inc(x_1);
x_67 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_1, x_3, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_65);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
lean_ctor_set(x_67, 0, x_38);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_38);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_67, 1);
x_75 = lean_ctor_get(x_67, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_68, 0);
lean_inc(x_76);
lean_dec(x_68);
x_77 = lean_unbox(x_39);
x_78 = l_Lean_ConstantInfo_hasValue(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_dec(x_65);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_67, 0, x_38);
return x_67;
}
else
{
uint8_t x_79; 
lean_inc(x_1);
lean_inc(x_65);
x_79 = l_Lean_Compiler_hasMacroInlineAttribute(x_65, x_1);
if (x_79 == 0)
{
lean_object* x_80; 
lean_free_object(x_67);
lean_inc(x_1);
lean_inc(x_65);
x_80 = lean_get_implemented_by(x_65, x_1);
if (lean_obj_tag(x_80) == 0)
{
x_40 = x_65;
x_41 = x_74;
x_42 = x_79;
goto block_58;
}
else
{
lean_dec(x_80);
x_40 = x_65;
x_41 = x_74;
x_42 = x_78;
goto block_58;
}
}
else
{
lean_dec(x_65);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_67, 0, x_38);
return x_67;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_67, 1);
lean_inc(x_81);
lean_dec(x_67);
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
lean_dec(x_68);
x_83 = lean_unbox(x_39);
x_84 = l_Lean_ConstantInfo_hasValue(x_82, x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_65);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_38);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
else
{
uint8_t x_86; 
lean_inc(x_1);
lean_inc(x_65);
x_86 = l_Lean_Compiler_hasMacroInlineAttribute(x_65, x_1);
if (x_86 == 0)
{
lean_object* x_87; 
lean_inc(x_1);
lean_inc(x_65);
x_87 = lean_get_implemented_by(x_65, x_1);
if (lean_obj_tag(x_87) == 0)
{
x_40 = x_65;
x_41 = x_81;
x_42 = x_86;
goto block_58;
}
else
{
lean_dec(x_87);
x_40 = x_65;
x_41 = x_81;
x_42 = x_84;
goto block_58;
}
}
else
{
lean_object* x_88; 
lean_dec(x_65);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_81);
return x_88;
}
}
}
}
}
else
{
lean_dec(x_65);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_61, 0, x_39);
return x_61;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_61, 0);
x_90 = lean_ctor_get(x_61, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_61);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_1);
lean_inc(x_91);
x_92 = l_Lean_isExtern(x_91, x_1);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_inc(x_1);
x_93 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_1, x_3, x_90);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_91);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
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
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_38);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
lean_dec(x_94);
x_101 = lean_unbox(x_39);
x_102 = l_Lean_ConstantInfo_hasValue(x_100, x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_91);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_99)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_99;
}
lean_ctor_set(x_103, 0, x_38);
lean_ctor_set(x_103, 1, x_98);
return x_103;
}
else
{
uint8_t x_104; 
lean_inc(x_1);
lean_inc(x_91);
x_104 = l_Lean_Compiler_hasMacroInlineAttribute(x_91, x_1);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_99);
lean_inc(x_1);
lean_inc(x_91);
x_105 = lean_get_implemented_by(x_91, x_1);
if (lean_obj_tag(x_105) == 0)
{
x_40 = x_91;
x_41 = x_98;
x_42 = x_104;
goto block_58;
}
else
{
lean_dec(x_105);
x_40 = x_91;
x_41 = x_98;
x_42 = x_102;
goto block_58;
}
}
else
{
lean_object* x_106; 
lean_dec(x_91);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_99)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_99;
}
lean_ctor_set(x_106, 0, x_38);
lean_ctor_set(x_106, 1, x_98);
return x_106;
}
}
}
}
else
{
lean_object* x_107; 
lean_dec(x_91);
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_39);
lean_ctor_set(x_107, 1, x_90);
return x_107;
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_38);
lean_ctor_set(x_108, 1, x_60);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isMatcher___at___Lean_Compiler_LCNF_shouldGenerateCode_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 3);
x_26 = l_Lean_maxRecDepth;
x_27 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_1, x_26);
x_28 = lean_ctor_get(x_9, 5);
x_29 = lean_ctor_get(x_9, 6);
x_30 = lean_ctor_get(x_9, 7);
x_31 = lean_ctor_get(x_9, 8);
x_32 = lean_ctor_get(x_9, 9);
x_33 = lean_ctor_get(x_9, 10);
x_34 = lean_ctor_get(x_9, 11);
x_35 = lean_ctor_get_uint8(x_9, sizeof(void*)*13 + 1);
x_36 = lean_ctor_get(x_9, 12);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_37 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_1);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_27);
lean_ctor_set(x_37, 5, x_28);
lean_ctor_set(x_37, 6, x_29);
lean_ctor_set(x_37, 7, x_30);
lean_ctor_set(x_37, 8, x_31);
lean_ctor_set(x_37, 9, x_32);
lean_ctor_set(x_37, 10, x_33);
lean_ctor_set(x_37, 11, x_34);
lean_ctor_set(x_37, 12, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_37, sizeof(void*)*13 + 1, x_35);
lean_inc(x_3);
x_38 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___redArg(x_3, x_37, x_11);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_3);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_12 = x_6;
x_13 = x_7;
x_14 = x_37;
x_15 = x_10;
x_16 = x_41;
goto block_22;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 1);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_37);
lean_inc(x_5);
x_45 = l_Lean_Compiler_LCNF_ppDecl_x27(x_5, x_37, x_10, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_mk_string_unchecked("size: ", 6, 6);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = l_Lean_Compiler_LCNF_Decl_size(x_5);
x_51 = l___private_Init_Data_Repr_0__Nat_reprFast(x_50);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_MessageData_ofFormat(x_52);
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_53);
lean_ctor_set(x_38, 0, x_49);
x_54 = lean_mk_string_unchecked("\n", 1, 1);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_38);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_MessageData_ofFormat(x_46);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_mk_string_unchecked("", 0, 0);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_3, x_61, x_7, x_37, x_10, x_47);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_12 = x_6;
x_13 = x_7;
x_14 = x_37;
x_15 = x_10;
x_16 = x_63;
goto block_22;
}
else
{
uint8_t x_64; 
lean_free_object(x_38);
lean_dec(x_37);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_45);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_38, 1);
lean_inc(x_68);
lean_dec(x_38);
lean_inc(x_10);
lean_inc(x_37);
lean_inc(x_5);
x_69 = l_Lean_Compiler_LCNF_ppDecl_x27(x_5, x_37, x_10, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_mk_string_unchecked("size: ", 6, 6);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = l_Lean_Compiler_LCNF_Decl_size(x_5);
x_75 = l___private_Init_Data_Repr_0__Nat_reprFast(x_74);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_MessageData_ofFormat(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("\n", 1, 1);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_MessageData_ofFormat(x_70);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("", 0, 0);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_3, x_86, x_7, x_37, x_10, x_71);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_12 = x_6;
x_13 = x_7;
x_14 = x_37;
x_15 = x_10;
x_16 = x_88;
goto block_22;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_37);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = lean_ctor_get(x_69, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_69, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_91 = x_69;
} else {
 lean_dec_ref(x_69);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = l_Lean_Compiler_compiler_check;
x_19 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_4);
x_21 = l_Lean_Compiler_LCNF_Decl_check(x_5, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_5);
x_13 = lean_box(0);
x_70 = lean_mk_string_unchecked("Compiler", 8, 8);
x_71 = lean_mk_string_unchecked("stat", 4, 4);
lean_inc(x_70);
x_72 = l_Lean_Name_mkStr2(x_70, x_71);
lean_inc(x_72);
x_73 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___redArg(x_72, x_8, x_10);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_103; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_array_uget(x_2, x_4);
x_103 = lean_unbox(x_75);
lean_dec(x_75);
if (x_103 == 0)
{
lean_free_object(x_73);
lean_dec(x_72);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_76;
goto block_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_104 = lean_mk_string_unchecked("", 0, 0);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_ctor_get(x_77, 0);
lean_inc(x_106);
x_107 = l_Lean_MessageData_ofName(x_106);
lean_inc(x_105);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_107);
lean_ctor_set(x_73, 0, x_105);
x_108 = lean_mk_string_unchecked(" : ", 3, 3);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_73);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Compiler_LCNF_Decl_size(x_77);
x_112 = l___private_Init_Data_Repr_0__Nat_reprFast(x_111);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_105);
x_117 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_72, x_116, x_7, x_8, x_9, x_76);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_118;
goto block_102;
}
block_102:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_83 = lean_st_ref_get(x_81, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_mk_string_unchecked("pp", 2, 2);
x_87 = lean_mk_string_unchecked("motives", 7, 7);
x_88 = lean_mk_string_unchecked("pi", 2, 2);
x_89 = l_Lean_Name_mkStr1(x_70);
x_90 = lean_ctor_get(x_80, 2);
lean_inc(x_90);
x_91 = l_Lean_Name_mkStr3(x_86, x_87, x_88);
x_92 = lean_box(0);
x_93 = l_Lean_diagnostics;
lean_inc(x_1);
x_94 = l_Lean_Name_append(x_89, x_1);
x_95 = lean_unbox(x_92);
x_96 = l_Lean_KVMap_setBool(x_90, x_91, x_95);
x_97 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_96, x_93);
x_98 = lean_box(x_97);
x_99 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0___boxed), 11, 7);
lean_closure_set(x_99, 0, x_96);
lean_closure_set(x_99, 1, x_98);
lean_closure_set(x_99, 2, x_94);
lean_closure_set(x_99, 3, x_13);
lean_closure_set(x_99, 4, x_77);
lean_closure_set(x_99, 5, x_78);
lean_closure_set(x_99, 6, x_79);
x_100 = lean_ctor_get(x_84, 0);
lean_inc(x_100);
lean_dec(x_84);
x_101 = l_Lean_Kernel_isDiagnosticsEnabled(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
if (x_97 == 0)
{
x_62 = x_99;
x_63 = x_80;
x_64 = x_81;
x_65 = x_85;
x_66 = x_97;
x_67 = x_11;
goto block_69;
}
else
{
x_21 = x_99;
x_22 = x_80;
x_23 = x_81;
x_24 = x_85;
x_25 = x_97;
goto block_61;
}
}
else
{
if (x_97 == 0)
{
x_21 = x_99;
x_22 = x_80;
x_23 = x_81;
x_24 = x_85;
x_25 = x_97;
goto block_61;
}
else
{
x_62 = x_99;
x_63 = x_80;
x_64 = x_81;
x_65 = x_85;
x_66 = x_97;
x_67 = x_11;
goto block_69;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_147; 
x_119 = lean_ctor_get(x_73, 0);
x_120 = lean_ctor_get(x_73, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_73);
x_121 = lean_array_uget(x_2, x_4);
x_147 = lean_unbox(x_119);
lean_dec(x_119);
if (x_147 == 0)
{
lean_dec(x_72);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_120;
goto block_146;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_148 = lean_mk_string_unchecked("", 0, 0);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
x_150 = lean_ctor_get(x_121, 0);
lean_inc(x_150);
x_151 = l_Lean_MessageData_ofName(x_150);
lean_inc(x_149);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_mk_string_unchecked(" : ", 3, 3);
x_154 = l_Lean_stringToMessageData(x_153);
lean_dec(x_153);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_Compiler_LCNF_Decl_size(x_121);
x_157 = l___private_Init_Data_Repr_0__Nat_reprFast(x_156);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_MessageData_ofFormat(x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_149);
x_162 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_72, x_161, x_7, x_8, x_9, x_120);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_163;
goto block_146;
}
block_146:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_127 = lean_st_ref_get(x_125, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_mk_string_unchecked("pp", 2, 2);
x_131 = lean_mk_string_unchecked("motives", 7, 7);
x_132 = lean_mk_string_unchecked("pi", 2, 2);
x_133 = l_Lean_Name_mkStr1(x_70);
x_134 = lean_ctor_get(x_124, 2);
lean_inc(x_134);
x_135 = l_Lean_Name_mkStr3(x_130, x_131, x_132);
x_136 = lean_box(0);
x_137 = l_Lean_diagnostics;
lean_inc(x_1);
x_138 = l_Lean_Name_append(x_133, x_1);
x_139 = lean_unbox(x_136);
x_140 = l_Lean_KVMap_setBool(x_134, x_135, x_139);
x_141 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_140, x_137);
x_142 = lean_box(x_141);
x_143 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0___boxed), 11, 7);
lean_closure_set(x_143, 0, x_140);
lean_closure_set(x_143, 1, x_142);
lean_closure_set(x_143, 2, x_138);
lean_closure_set(x_143, 3, x_13);
lean_closure_set(x_143, 4, x_121);
lean_closure_set(x_143, 5, x_122);
lean_closure_set(x_143, 6, x_123);
x_144 = lean_ctor_get(x_128, 0);
lean_inc(x_144);
lean_dec(x_128);
x_145 = l_Lean_Kernel_isDiagnosticsEnabled(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
if (x_141 == 0)
{
x_62 = x_143;
x_63 = x_124;
x_64 = x_125;
x_65 = x_129;
x_66 = x_141;
x_67 = x_11;
goto block_69;
}
else
{
x_21 = x_143;
x_22 = x_124;
x_23 = x_125;
x_24 = x_129;
x_25 = x_141;
goto block_61;
}
}
else
{
if (x_141 == 0)
{
x_21 = x_143;
x_22 = x_124;
x_23 = x_125;
x_24 = x_129;
x_25 = x_141;
goto block_61;
}
else
{
x_62 = x_143;
x_63 = x_124;
x_64 = x_125;
x_65 = x_129;
x_66 = x_141;
x_67 = x_11;
goto block_69;
}
}
}
}
block_20:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_13;
x_10 = x_15;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
block_61:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_st_ref_take(x_23, x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = l_Lean_Kernel_enableDiag(x_30, x_25);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 3);
lean_inc(x_34);
x_35 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_36);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_36);
x_37 = lean_ctor_get(x_28, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 7);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_26);
lean_ctor_set(x_40, 5, x_37);
lean_ctor_set(x_40, 6, x_38);
lean_ctor_set(x_40, 7, x_39);
x_41 = lean_st_ref_set(x_23, x_40, x_29);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_apply_4(x_21, x_13, x_22, x_23, x_42);
x_14 = x_43;
goto block_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = lean_ctor_get(x_26, 0);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_26);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = l_Lean_Kernel_enableDiag(x_46, x_25);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_inc(x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_ctor_get(x_44, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_44, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 7);
lean_inc(x_56);
lean_dec(x_44);
x_57 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_49);
lean_ctor_set(x_57, 3, x_50);
lean_ctor_set(x_57, 4, x_53);
lean_ctor_set(x_57, 5, x_54);
lean_ctor_set(x_57, 6, x_55);
lean_ctor_set(x_57, 7, x_56);
x_58 = lean_st_ref_set(x_23, x_57, x_45);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_apply_4(x_21, x_13, x_22, x_23, x_59);
x_14 = x_60;
goto block_20;
}
}
block_69:
{
if (x_67 == 0)
{
x_21 = x_62;
x_22 = x_63;
x_23 = x_64;
x_24 = x_65;
x_25 = x_66;
goto block_61;
}
else
{
lean_object* x_68; 
x_68 = lean_apply_4(x_62, x_13, x_63, x_64, x_65);
x_14 = x_68;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_5);
x_13 = lean_box(0);
x_70 = lean_mk_string_unchecked("Compiler", 8, 8);
x_71 = lean_mk_string_unchecked("stat", 4, 4);
lean_inc(x_70);
x_72 = l_Lean_Name_mkStr2(x_70, x_71);
lean_inc(x_72);
x_73 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___redArg(x_72, x_8, x_10);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_103; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
x_77 = lean_array_uget(x_2, x_4);
x_103 = lean_unbox(x_75);
lean_dec(x_75);
if (x_103 == 0)
{
lean_free_object(x_73);
lean_dec(x_72);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_76;
goto block_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_104 = lean_mk_string_unchecked("", 0, 0);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_ctor_get(x_77, 0);
lean_inc(x_106);
x_107 = l_Lean_MessageData_ofName(x_106);
lean_inc(x_105);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_107);
lean_ctor_set(x_73, 0, x_105);
x_108 = lean_mk_string_unchecked(" : ", 3, 3);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_73);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Compiler_LCNF_Decl_size(x_77);
x_112 = l___private_Init_Data_Repr_0__Nat_reprFast(x_111);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_105);
x_117 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_72, x_116, x_7, x_8, x_9, x_76);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_118;
goto block_102;
}
block_102:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_83 = lean_st_ref_get(x_81, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_mk_string_unchecked("pp", 2, 2);
x_87 = lean_mk_string_unchecked("motives", 7, 7);
x_88 = lean_mk_string_unchecked("pi", 2, 2);
x_89 = l_Lean_Name_mkStr1(x_70);
x_90 = lean_ctor_get(x_80, 2);
lean_inc(x_90);
x_91 = l_Lean_Name_mkStr3(x_86, x_87, x_88);
x_92 = lean_box(0);
x_93 = l_Lean_diagnostics;
lean_inc(x_1);
x_94 = l_Lean_Name_append(x_89, x_1);
x_95 = lean_unbox(x_92);
x_96 = l_Lean_KVMap_setBool(x_90, x_91, x_95);
x_97 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_96, x_93);
x_98 = lean_box(x_97);
x_99 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0___boxed), 11, 7);
lean_closure_set(x_99, 0, x_96);
lean_closure_set(x_99, 1, x_98);
lean_closure_set(x_99, 2, x_94);
lean_closure_set(x_99, 3, x_13);
lean_closure_set(x_99, 4, x_77);
lean_closure_set(x_99, 5, x_78);
lean_closure_set(x_99, 6, x_79);
x_100 = lean_ctor_get(x_84, 0);
lean_inc(x_100);
lean_dec(x_84);
x_101 = l_Lean_Kernel_isDiagnosticsEnabled(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
if (x_97 == 0)
{
x_62 = x_97;
x_63 = x_99;
x_64 = x_80;
x_65 = x_85;
x_66 = x_81;
x_67 = x_11;
goto block_69;
}
else
{
x_21 = x_97;
x_22 = x_80;
x_23 = x_99;
x_24 = x_85;
x_25 = x_81;
goto block_61;
}
}
else
{
if (x_97 == 0)
{
x_21 = x_97;
x_22 = x_80;
x_23 = x_99;
x_24 = x_85;
x_25 = x_81;
goto block_61;
}
else
{
x_62 = x_97;
x_63 = x_99;
x_64 = x_80;
x_65 = x_85;
x_66 = x_81;
x_67 = x_11;
goto block_69;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_147; 
x_119 = lean_ctor_get(x_73, 0);
x_120 = lean_ctor_get(x_73, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_73);
x_121 = lean_array_uget(x_2, x_4);
x_147 = lean_unbox(x_119);
lean_dec(x_119);
if (x_147 == 0)
{
lean_dec(x_72);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_120;
goto block_146;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_148 = lean_mk_string_unchecked("", 0, 0);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
x_150 = lean_ctor_get(x_121, 0);
lean_inc(x_150);
x_151 = l_Lean_MessageData_ofName(x_150);
lean_inc(x_149);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_mk_string_unchecked(" : ", 3, 3);
x_154 = l_Lean_stringToMessageData(x_153);
lean_dec(x_153);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_Compiler_LCNF_Decl_size(x_121);
x_157 = l___private_Init_Data_Repr_0__Nat_reprFast(x_156);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_MessageData_ofFormat(x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_149);
x_162 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_72, x_161, x_7, x_8, x_9, x_120);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_122 = x_6;
x_123 = x_7;
x_124 = x_8;
x_125 = x_9;
x_126 = x_163;
goto block_146;
}
block_146:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_127 = lean_st_ref_get(x_125, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_mk_string_unchecked("pp", 2, 2);
x_131 = lean_mk_string_unchecked("motives", 7, 7);
x_132 = lean_mk_string_unchecked("pi", 2, 2);
x_133 = l_Lean_Name_mkStr1(x_70);
x_134 = lean_ctor_get(x_124, 2);
lean_inc(x_134);
x_135 = l_Lean_Name_mkStr3(x_130, x_131, x_132);
x_136 = lean_box(0);
x_137 = l_Lean_diagnostics;
lean_inc(x_1);
x_138 = l_Lean_Name_append(x_133, x_1);
x_139 = lean_unbox(x_136);
x_140 = l_Lean_KVMap_setBool(x_134, x_135, x_139);
x_141 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_140, x_137);
x_142 = lean_box(x_141);
x_143 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0___boxed), 11, 7);
lean_closure_set(x_143, 0, x_140);
lean_closure_set(x_143, 1, x_142);
lean_closure_set(x_143, 2, x_138);
lean_closure_set(x_143, 3, x_13);
lean_closure_set(x_143, 4, x_121);
lean_closure_set(x_143, 5, x_122);
lean_closure_set(x_143, 6, x_123);
x_144 = lean_ctor_get(x_128, 0);
lean_inc(x_144);
lean_dec(x_128);
x_145 = l_Lean_Kernel_isDiagnosticsEnabled(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
if (x_141 == 0)
{
x_62 = x_141;
x_63 = x_143;
x_64 = x_124;
x_65 = x_129;
x_66 = x_125;
x_67 = x_11;
goto block_69;
}
else
{
x_21 = x_141;
x_22 = x_124;
x_23 = x_143;
x_24 = x_129;
x_25 = x_125;
goto block_61;
}
}
else
{
if (x_141 == 0)
{
x_21 = x_141;
x_22 = x_124;
x_23 = x_143;
x_24 = x_129;
x_25 = x_125;
goto block_61;
}
else
{
x_62 = x_141;
x_63 = x_143;
x_64 = x_124;
x_65 = x_129;
x_66 = x_125;
x_67 = x_11;
goto block_69;
}
}
}
}
block_20:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0(x_1, x_2, x_3, x_18, x_13, x_6, x_7, x_8, x_9, x_15);
return x_19;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
block_61:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_st_ref_take(x_25, x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = l_Lean_Kernel_enableDiag(x_30, x_21);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 3);
lean_inc(x_34);
x_35 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_36);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_36);
x_37 = lean_ctor_get(x_28, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 7);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_26);
lean_ctor_set(x_40, 5, x_37);
lean_ctor_set(x_40, 6, x_38);
lean_ctor_set(x_40, 7, x_39);
x_41 = lean_st_ref_set(x_25, x_40, x_29);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_apply_4(x_23, x_13, x_22, x_25, x_42);
x_14 = x_43;
goto block_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = lean_ctor_get(x_26, 0);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_26);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = l_Lean_Kernel_enableDiag(x_46, x_21);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_inc(x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_ctor_get(x_44, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_44, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 7);
lean_inc(x_56);
lean_dec(x_44);
x_57 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_49);
lean_ctor_set(x_57, 3, x_50);
lean_ctor_set(x_57, 4, x_53);
lean_ctor_set(x_57, 5, x_54);
lean_ctor_set(x_57, 6, x_55);
lean_ctor_set(x_57, 7, x_56);
x_58 = lean_st_ref_set(x_25, x_57, x_45);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_apply_4(x_23, x_13, x_22, x_25, x_59);
x_14 = x_60;
goto block_20;
}
}
block_69:
{
if (x_67 == 0)
{
x_21 = x_62;
x_22 = x_64;
x_23 = x_63;
x_24 = x_65;
x_25 = x_66;
goto block_61;
}
else
{
lean_object* x_68; 
x_68 = lean_apply_4(x_63, x_13, x_64, x_66, x_65);
x_14 = x_68;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_array_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0(x_1, x_2, x_9, x_11, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_5, 2);
lean_inc(x_16);
x_17 = l_Lean_Compiler_compiler_check;
x_18 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
lean_object* x_19; 
lean_free_object(x_12);
x_19 = l_Lean_Compiler_LCNF_checkDeadLocalDecls(x_2, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
x_22 = l_Lean_Compiler_compiler_check;
x_23 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Compiler_LCNF_checkDeadLocalDecls(x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___lam__0(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_checkpoint_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkpoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_checkpoint(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_PersistentArray_toArray___redArg(x_13);
lean_dec(x_13);
x_15 = lean_array_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_st_ref_get(x_7, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_5, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(x_15, x_17, x_14);
x_26 = lean_ctor_get(x_6, 2);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_28);
lean_dec(x_28);
x_30 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_inc(x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_30);
lean_inc(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_30);
lean_inc(x_30);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_30);
x_37 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_16);
lean_ctor_set(x_37, 2, x_16);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
lean_ctor_set(x_37, 8, x_36);
x_38 = lean_st_ref_take(x_7, x_24);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_4);
lean_ctor_set(x_42, 2, x_25);
lean_inc(x_26);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_29);
lean_ctor_set(x_43, 3, x_26);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 1, x_42);
lean_ctor_set(x_38, 0, x_43);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 3);
lean_inc(x_47);
x_48 = lean_ctor_get_uint64(x_47, sizeof(void*)*1);
lean_dec(x_47);
lean_ctor_set(x_21, 1, x_38);
lean_ctor_set(x_21, 0, x_3);
x_49 = l_Lean_PersistentArray_push___redArg(x_1, x_21);
x_50 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint64(x_50, sizeof(void*)*1, x_48);
x_51 = lean_ctor_get(x_40, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_40, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_40, 6);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 7);
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_45);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_52);
lean_ctor_set(x_55, 6, x_53);
lean_ctor_set(x_55, 7, x_54);
x_56 = lean_st_ref_set(x_7, x_55, x_41);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_63 = lean_ctor_get(x_38, 0);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_38);
x_65 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_4);
lean_ctor_set(x_65, 2, x_25);
lean_inc(x_26);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_37);
lean_ctor_set(x_66, 2, x_29);
lean_ctor_set(x_66, 3, x_26);
x_67 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 3);
lean_inc(x_71);
x_72 = lean_ctor_get_uint64(x_71, sizeof(void*)*1);
lean_dec(x_71);
lean_ctor_set(x_21, 1, x_67);
lean_ctor_set(x_21, 0, x_3);
x_73 = l_Lean_PersistentArray_push___redArg(x_1, x_21);
x_74 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set_uint64(x_74, sizeof(void*)*1, x_72);
x_75 = lean_ctor_get(x_63, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_63, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_63, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_63, 7);
lean_inc(x_78);
lean_dec(x_63);
x_79 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_69);
lean_ctor_set(x_79, 2, x_70);
lean_ctor_set(x_79, 3, x_74);
lean_ctor_set(x_79, 4, x_75);
lean_ctor_set(x_79, 5, x_76);
lean_ctor_set(x_79, 6, x_77);
lean_ctor_set(x_79, 7, x_78);
x_80 = lean_st_ref_set(x_7, x_79, x_64);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = lean_box(0);
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
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_85 = lean_ctor_get(x_21, 0);
x_86 = lean_ctor_get(x_21, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_21);
x_87 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20_spec__21_spec__21(x_15, x_17, x_14);
x_88 = lean_ctor_get(x_6, 2);
x_89 = lean_ctor_get(x_19, 0);
lean_inc(x_89);
lean_dec(x_19);
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
lean_dec(x_85);
x_91 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_90);
lean_dec(x_90);
x_92 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_92);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_inc(x_92);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_92);
lean_inc(x_92);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
lean_inc(x_92);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_92);
lean_inc(x_92);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_92);
x_99 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_99, 0, x_16);
lean_ctor_set(x_99, 1, x_16);
lean_ctor_set(x_99, 2, x_16);
lean_ctor_set(x_99, 3, x_93);
lean_ctor_set(x_99, 4, x_94);
lean_ctor_set(x_99, 5, x_95);
lean_ctor_set(x_99, 6, x_96);
lean_ctor_set(x_99, 7, x_97);
lean_ctor_set(x_99, 8, x_98);
x_100 = lean_st_ref_take(x_7, x_86);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_104, 0, x_2);
lean_ctor_set(x_104, 1, x_4);
lean_ctor_set(x_104, 2, x_87);
lean_inc(x_88);
x_105 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_105, 0, x_89);
lean_ctor_set(x_105, 1, x_99);
lean_ctor_set(x_105, 2, x_91);
lean_ctor_set(x_105, 3, x_88);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(3, 2, 0);
} else {
 x_106 = x_103;
 lean_ctor_set_tag(x_106, 3);
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 3);
lean_inc(x_110);
x_111 = lean_ctor_get_uint64(x_110, sizeof(void*)*1);
lean_dec(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_3);
lean_ctor_set(x_112, 1, x_106);
x_113 = l_Lean_PersistentArray_push___redArg(x_1, x_112);
x_114 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set_uint64(x_114, sizeof(void*)*1, x_111);
x_115 = lean_ctor_get(x_101, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_101, 5);
lean_inc(x_116);
x_117 = lean_ctor_get(x_101, 6);
lean_inc(x_117);
x_118 = lean_ctor_get(x_101, 7);
lean_inc(x_118);
lean_dec(x_101);
x_119 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_119, 0, x_107);
lean_ctor_set(x_119, 1, x_108);
lean_ctor_set(x_119, 2, x_109);
lean_ctor_set(x_119, 3, x_114);
lean_ctor_set(x_119, 4, x_115);
lean_ctor_set(x_119, 5, x_116);
lean_ctor_set(x_119, 6, x_117);
lean_ctor_set(x_119, 7, x_118);
x_120 = lean_st_ref_set(x_7, x_119, x_102);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___redArg(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_io_get_num_heartbeats(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_io_mono_nanos_now(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___redArg(x_1, x_5, x_2, x_3, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___redArg(x_4, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; double x_12; uint8_t x_13; double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_28; lean_object* x_29; lean_object* x_30; double x_31; double x_32; lean_object* x_33; uint8_t x_34; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; double x_55; double x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; double x_85; double x_86; lean_object* x_87; uint8_t x_88; double x_89; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; double x_99; double x_100; lean_object* x_101; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_200; 
lean_inc(x_1);
x_47 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___redArg(x_1, x_8, x_10);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_93 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__0), 1, 0);
x_94 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__1), 1, 0);
x_95 = lean_ctor_get(x_8, 2);
lean_inc(x_95);
x_200 = lean_unbox(x_48);
if (x_200 == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = l_Lean_trace_profiler;
x_202 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_95, x_201);
if (x_202 == 0)
{
lean_object* x_203; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_49);
return x_203;
}
else
{
goto block_199;
}
}
else
{
goto block_199;
}
block_27:
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(0u);
if (x_13 == 0)
{
double x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_float_of_nat(x_19);
x_21 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set_float(x_21, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_21, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2 + 16, x_4);
x_22 = lean_box(0);
x_23 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__2(x_11, x_16, x_17, x_15, x_21, x_22, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_15);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_12);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_4);
x_25 = lean_box(0);
x_26 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__2(x_11, x_16, x_17, x_15, x_24, x_25, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_15);
return x_26;
}
}
block_46:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_8, 5);
lean_inc(x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = lean_apply_6(x_2, x_33, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_36) == 0)
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_11 = x_28;
x_12 = x_32;
x_13 = x_34;
x_14 = x_31;
x_15 = x_29;
x_16 = x_35;
x_17 = x_37;
x_18 = x_38;
goto block_27;
}
else
{
uint8_t x_39; 
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_ctor_set_tag(x_36, 1);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_11 = x_28;
x_12 = x_32;
x_13 = x_34;
x_14 = x_31;
x_15 = x_29;
x_16 = x_35;
x_17 = x_45;
x_18 = x_43;
goto block_27;
}
}
block_80:
{
uint8_t x_60; 
x_60 = lean_unbox(x_48);
lean_dec(x_48);
if (x_60 == 0)
{
if (x_59 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_st_ref_take(x_9, x_53);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 3);
lean_inc(x_67);
x_68 = lean_ctor_get_uint64(x_67, sizeof(void*)*1);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_PersistentArray_append___redArg(x_54, x_69);
lean_dec(x_69);
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
x_77 = lean_st_ref_set(x_9, x_76, x_63);
lean_dec(x_9);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___redArg(x_57, x_78);
lean_dec(x_57);
return x_79;
}
else
{
lean_dec(x_54);
x_28 = x_51;
x_29 = x_52;
x_30 = x_53;
x_31 = x_55;
x_32 = x_56;
x_33 = x_57;
x_34 = x_58;
goto block_46;
}
}
else
{
lean_dec(x_54);
x_28 = x_51;
x_29 = x_52;
x_30 = x_53;
x_31 = x_55;
x_32 = x_56;
x_33 = x_57;
x_34 = x_58;
goto block_46;
}
}
block_92:
{
double x_90; uint8_t x_91; 
x_90 = lean_float_sub(x_86, x_85);
x_91 = lean_float_decLt(x_89, x_90);
x_51 = x_81;
x_52 = x_82;
x_53 = x_83;
x_54 = x_84;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_91;
goto block_80;
}
block_115:
{
lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_trace_profiler;
x_103 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_95, x_102);
if (x_103 == 0)
{
lean_dec(x_95);
lean_inc(x_98);
x_51 = x_96;
x_52 = x_98;
x_53 = x_101;
x_54 = x_97;
x_55 = x_99;
x_56 = x_100;
x_57 = x_98;
x_58 = x_103;
x_59 = x_103;
goto block_80;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_trace_profiler_useHeartbeats;
x_105 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_95, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; double x_108; lean_object* x_109; double x_110; double x_111; 
x_106 = l_Lean_trace_profiler_threshold;
x_107 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_95, x_106);
lean_dec(x_95);
x_108 = lean_float_of_nat(x_107);
x_109 = lean_unsigned_to_nat(1000u);
x_110 = lean_float_of_nat(x_109);
x_111 = lean_float_div(x_108, x_110);
lean_inc(x_98);
x_81 = x_96;
x_82 = x_98;
x_83 = x_101;
x_84 = x_97;
x_85 = x_99;
x_86 = x_100;
x_87 = x_98;
x_88 = x_103;
x_89 = x_111;
goto block_92;
}
else
{
lean_object* x_112; lean_object* x_113; double x_114; 
x_112 = l_Lean_trace_profiler_threshold;
x_113 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_95, x_112);
lean_dec(x_95);
x_114 = lean_float_of_nat(x_113);
lean_inc(x_98);
x_81 = x_96;
x_82 = x_98;
x_83 = x_101;
x_84 = x_97;
x_85 = x_99;
x_86 = x_100;
x_87 = x_98;
x_88 = x_103;
x_89 = x_114;
goto block_92;
}
}
}
block_145:
{
lean_object* x_123; 
x_123 = lean_apply_1(x_120, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; double x_126; lean_object* x_127; double x_128; double x_129; double x_130; double x_131; 
lean_dec(x_119);
lean_dec(x_50);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_float_of_nat(x_117);
x_127 = lean_unsigned_to_nat(1000000000u);
x_128 = lean_float_of_nat(x_127);
x_129 = lean_float_div(x_126, x_128);
x_130 = lean_float_of_nat(x_124);
x_131 = lean_float_div(x_130, x_128);
x_96 = x_116;
x_97 = x_118;
x_98 = x_121;
x_99 = x_129;
x_100 = x_131;
x_101 = x_125;
goto block_115;
}
else
{
uint8_t x_132; 
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_95);
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_123);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_123, 0);
x_134 = lean_io_error_to_string(x_133);
x_135 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l_Lean_MessageData_ofFormat(x_135);
if (lean_is_scalar(x_50)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_50;
}
lean_ctor_set(x_137, 0, x_119);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_123, 0, x_137);
return x_123;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_123, 0);
x_139 = lean_ctor_get(x_123, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_123);
x_140 = lean_io_error_to_string(x_138);
x_141 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = l_Lean_MessageData_ofFormat(x_141);
if (lean_is_scalar(x_50)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_50;
}
lean_ctor_set(x_143, 0, x_119);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_139);
return x_144;
}
}
}
block_171:
{
lean_object* x_153; 
x_153 = lean_apply_1(x_150, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; double x_156; double x_157; 
lean_dec(x_149);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_float_of_nat(x_147);
x_157 = lean_float_of_nat(x_154);
x_96 = x_146;
x_97 = x_148;
x_98 = x_151;
x_99 = x_156;
x_100 = x_157;
x_101 = x_155;
goto block_115;
}
else
{
uint8_t x_158; 
lean_dec(x_151);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_95);
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_153);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_153, 0);
x_160 = lean_io_error_to_string(x_159);
x_161 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_MessageData_ofFormat(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_149);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_153, 0, x_163);
return x_153;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_153, 0);
x_165 = lean_ctor_get(x_153, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_153);
x_166 = lean_io_error_to_string(x_164);
x_167 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = l_Lean_MessageData_ofFormat(x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_149);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_165);
return x_170;
}
}
}
block_199:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(x_9, x_49);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_trace_profiler_useHeartbeats;
x_176 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_95, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_93);
x_177 = lean_ctor_get(x_8, 5);
lean_inc(x_177);
x_178 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__1(x_174);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_181 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_182);
lean_inc(x_173);
x_116 = x_173;
x_117 = x_179;
x_118 = x_173;
x_119 = x_177;
x_120 = x_94;
x_121 = x_184;
x_122 = x_183;
goto block_145;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 1);
lean_inc(x_186);
lean_dec(x_181);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_185);
lean_inc(x_173);
x_116 = x_173;
x_117 = x_179;
x_118 = x_173;
x_119 = x_177;
x_120 = x_94;
x_121 = x_187;
x_122 = x_186;
goto block_145;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_94);
lean_dec(x_50);
x_188 = lean_ctor_get(x_8, 5);
lean_inc(x_188);
x_189 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__0(x_174);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_192 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_193);
lean_inc(x_173);
x_146 = x_173;
x_147 = x_190;
x_148 = x_173;
x_149 = x_188;
x_150 = x_93;
x_151 = x_195;
x_152 = x_194;
goto block_171;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_196);
lean_inc(x_173);
x_146 = x_173;
x_147 = x_190;
x_148 = x_173;
x_149 = x_188;
x_150 = x_93;
x_151 = x_198;
x_152 = x_197;
goto block_171;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Compiler_LCNF_toDecl(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_16, x_2, x_13);
x_2 = x_19;
x_3 = x_20;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_25; 
x_8 = lean_mk_string_unchecked("new compiler phase: ", 20, 20);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
switch (x_25) {
case 0:
{
lean_object* x_26; 
x_26 = lean_mk_string_unchecked("base", 4, 4);
x_10 = x_26;
goto block_24;
}
case 1:
{
lean_object* x_27; 
x_27 = lean_mk_string_unchecked("mono", 4, 4);
x_10 = x_27;
goto block_24;
}
default: 
{
lean_object* x_28; 
x_28 = lean_mk_string_unchecked("impure", 6, 6);
x_10 = x_28;
goto block_24;
}
}
block_24:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_MessageData_ofFormat(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(", pass: ", 8, 8);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
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
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_1);
x_11 = lean_apply_6(x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__0___boxed), 7, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_mk_string_unchecked("Compiler", 8, 8);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__1___boxed), 8, 3);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_4);
x_20 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(x_15, x_13, x_19, x_10, x_20, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Compiler_LCNF_checkpoint(x_25, x_22, x_27, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_4 = x_22;
x_9 = x_29;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_4);
x_11 = lean_mk_string_unchecked("Compiler", 8, 8);
x_12 = lean_array_uget(x_1, x_3);
x_13 = lean_mk_string_unchecked("IR", 2, 2);
x_14 = l_Lean_Name_mkStr2(x_11, x_13);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_IR_LogEntry_fmt(x_12);
x_18 = l_Lean_MessageData_ofFormat(x_17);
lean_inc(x_16);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_14, x_20, x_5, x_6, x_7, x_8);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_3, x_25);
x_3 = x_26;
x_4 = x_23;
x_8 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_4);
x_19 = lean_array_uget(x_1, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Compiler_LCNF_getDeclAt_x3f___redArg(x_20, x_22, x_8, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_box(0);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_23);
lean_dec(x_19);
x_28 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Main", 23, 23);
x_29 = lean_mk_string_unchecked("Lean.Compiler.LCNF.PassManager.run", 34, 34);
x_30 = lean_unsigned_to_nat(88u);
x_31 = lean_unsigned_to_nat(52u);
x_32 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_33 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_28, x_29, x_30, x_31, x_32);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_panic___at___Lean_Compiler_LCNF_Decl_save_spec__0(x_33, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_10 = x_27;
x_11 = x_35;
goto block_16;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_34;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Compiler_LCNF_ppDecl_x27(x_37, x_7, x_8, x_26);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_mk_string_unchecked("Compiler", 8, 8);
x_42 = lean_mk_string_unchecked("result", 6, 6);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = lean_mk_string_unchecked("size: ", 6, 6);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_Compiler_LCNF_Decl_size(x_19);
lean_dec(x_19);
x_47 = l___private_Init_Data_Repr_0__Nat_reprFast(x_46);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 0, x_47);
x_48 = l_Lean_MessageData_ofFormat(x_25);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_48);
lean_ctor_set(x_23, 0, x_45);
x_49 = lean_mk_string_unchecked("\n", 1, 1);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_23);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofFormat(x_39);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("", 0, 0);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_43, x_56, x_6, x_7, x_8, x_40);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_10 = x_27;
x_11 = x_58;
goto block_16;
}
else
{
uint8_t x_59; 
lean_free_object(x_25);
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_38);
if (x_59 == 0)
{
return x_38;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_38);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_25, 0);
lean_inc(x_63);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
x_64 = l_Lean_Compiler_LCNF_ppDecl_x27(x_63, x_7, x_8, x_26);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_mk_string_unchecked("Compiler", 8, 8);
x_68 = lean_mk_string_unchecked("result", 6, 6);
x_69 = l_Lean_Name_mkStr2(x_67, x_68);
x_70 = lean_mk_string_unchecked("size: ", 6, 6);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = l_Lean_Compiler_LCNF_Decl_size(x_19);
lean_dec(x_19);
x_73 = l___private_Init_Data_Repr_0__Nat_reprFast(x_72);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_MessageData_ofFormat(x_74);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_75);
lean_ctor_set(x_23, 0, x_71);
x_76 = lean_mk_string_unchecked("\n", 1, 1);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_23);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_65);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_69, x_83, x_6, x_7, x_8, x_66);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_10 = x_27;
x_11 = x_85;
goto block_16;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_ctor_get(x_64, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_64, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_88 = x_64;
} else {
 lean_dec_ref(x_64);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_23, 0);
x_91 = lean_ctor_get(x_23, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_23);
x_92 = lean_box(0);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_19);
x_93 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Main", 23, 23);
x_94 = lean_mk_string_unchecked("Lean.Compiler.LCNF.PassManager.run", 34, 34);
x_95 = lean_unsigned_to_nat(88u);
x_96 = lean_unsigned_to_nat(52u);
x_97 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_98 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_93, x_94, x_95, x_96, x_97);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_99 = l_panic___at___Lean_Compiler_LCNF_Decl_save_spec__0(x_98, x_5, x_6, x_7, x_8, x_91);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_10 = x_92;
x_11 = x_100;
goto block_16;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_99;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_90, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_102 = x_90;
} else {
 lean_dec_ref(x_90);
 x_102 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
x_103 = l_Lean_Compiler_LCNF_ppDecl_x27(x_101, x_7, x_8, x_91);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_mk_string_unchecked("Compiler", 8, 8);
x_107 = lean_mk_string_unchecked("result", 6, 6);
x_108 = l_Lean_Name_mkStr2(x_106, x_107);
x_109 = lean_mk_string_unchecked("size: ", 6, 6);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
x_111 = l_Lean_Compiler_LCNF_Decl_size(x_19);
lean_dec(x_19);
x_112 = l___private_Init_Data_Repr_0__Nat_reprFast(x_111);
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(3, 1, 0);
} else {
 x_113 = x_102;
 lean_ctor_set_tag(x_113, 3);
}
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("\n", 1, 1);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_MessageData_ofFormat(x_104);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_mk_string_unchecked("", 0, 0);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_108, x_123, x_6, x_7, x_8, x_105);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_10 = x_92;
x_11 = x_125;
goto block_16;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_102);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = lean_ctor_get(x_103, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_103, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_128 = x_103;
} else {
 lean_dec_ref(x_103);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_4);
x_19 = lean_array_uget(x_1, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Compiler_LCNF_getDeclAt_x3f___redArg(x_20, x_22, x_8, x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_box(0);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_23);
lean_dec(x_19);
x_28 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Main", 23, 23);
x_29 = lean_mk_string_unchecked("Lean.Compiler.LCNF.PassManager.run", 34, 34);
x_30 = lean_unsigned_to_nat(88u);
x_31 = lean_unsigned_to_nat(52u);
x_32 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_33 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_28, x_29, x_30, x_31, x_32);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_panic___at___Lean_Compiler_LCNF_Decl_save_spec__0(x_33, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_10 = x_27;
x_11 = x_35;
goto block_16;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_34;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Compiler_LCNF_ppDecl_x27(x_37, x_7, x_8, x_26);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_mk_string_unchecked("Compiler", 8, 8);
x_42 = lean_mk_string_unchecked("result", 6, 6);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = lean_mk_string_unchecked("size: ", 6, 6);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_Compiler_LCNF_Decl_size(x_19);
lean_dec(x_19);
x_47 = l___private_Init_Data_Repr_0__Nat_reprFast(x_46);
lean_ctor_set_tag(x_25, 3);
lean_ctor_set(x_25, 0, x_47);
x_48 = l_Lean_MessageData_ofFormat(x_25);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_48);
lean_ctor_set(x_23, 0, x_45);
x_49 = lean_mk_string_unchecked("\n", 1, 1);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_23);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofFormat(x_39);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("", 0, 0);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_43, x_56, x_6, x_7, x_8, x_40);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_10 = x_27;
x_11 = x_58;
goto block_16;
}
else
{
uint8_t x_59; 
lean_free_object(x_25);
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_38);
if (x_59 == 0)
{
return x_38;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_38);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_25, 0);
lean_inc(x_63);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
x_64 = l_Lean_Compiler_LCNF_ppDecl_x27(x_63, x_7, x_8, x_26);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_mk_string_unchecked("Compiler", 8, 8);
x_68 = lean_mk_string_unchecked("result", 6, 6);
x_69 = l_Lean_Name_mkStr2(x_67, x_68);
x_70 = lean_mk_string_unchecked("size: ", 6, 6);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = l_Lean_Compiler_LCNF_Decl_size(x_19);
lean_dec(x_19);
x_73 = l___private_Init_Data_Repr_0__Nat_reprFast(x_72);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_MessageData_ofFormat(x_74);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_75);
lean_ctor_set(x_23, 0, x_71);
x_76 = lean_mk_string_unchecked("\n", 1, 1);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_23);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_65);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_69, x_83, x_6, x_7, x_8, x_66);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_10 = x_27;
x_11 = x_85;
goto block_16;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_23);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_ctor_get(x_64, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_64, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_88 = x_64;
} else {
 lean_dec_ref(x_64);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_23, 0);
x_91 = lean_ctor_get(x_23, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_23);
x_92 = lean_box(0);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_19);
x_93 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Main", 23, 23);
x_94 = lean_mk_string_unchecked("Lean.Compiler.LCNF.PassManager.run", 34, 34);
x_95 = lean_unsigned_to_nat(88u);
x_96 = lean_unsigned_to_nat(52u);
x_97 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_98 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_93, x_94, x_95, x_96, x_97);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_99 = l_panic___at___Lean_Compiler_LCNF_Decl_save_spec__0(x_98, x_5, x_6, x_7, x_8, x_91);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_10 = x_92;
x_11 = x_100;
goto block_16;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_99;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_90, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_102 = x_90;
} else {
 lean_dec_ref(x_90);
 x_102 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
x_103 = l_Lean_Compiler_LCNF_ppDecl_x27(x_101, x_7, x_8, x_91);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_mk_string_unchecked("Compiler", 8, 8);
x_107 = lean_mk_string_unchecked("result", 6, 6);
x_108 = l_Lean_Name_mkStr2(x_106, x_107);
x_109 = lean_mk_string_unchecked("size: ", 6, 6);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
x_111 = l_Lean_Compiler_LCNF_Decl_size(x_19);
lean_dec(x_19);
x_112 = l___private_Init_Data_Repr_0__Nat_reprFast(x_111);
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(3, 1, 0);
} else {
 x_113 = x_102;
 lean_ctor_set_tag(x_113, 3);
}
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("\n", 1, 1);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_MessageData_ofFormat(x_104);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_mk_string_unchecked("", 0, 0);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_addTrace___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__1___redArg(x_108, x_123, x_6, x_7, x_8, x_105);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_10 = x_92;
x_11 = x_125;
goto block_16;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_102);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = lean_ctor_get(x_103, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_103, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_128 = x_103;
} else {
 lean_dec_ref(x_103);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8_spec__8(x_1, x_2, x_14, x_10, x_5, x_6, x_7, x_8, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_shouldGenerateCode(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_19 = lean_unbox(x_11);
lean_dec(x_11);
if (x_19 == 0)
{
lean_dec(x_9);
x_13 = x_4;
goto block_18;
}
else
{
lean_object* x_20; 
x_20 = lean_array_push(x_4, x_9);
x_13 = x_20;
goto block_18;
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_7 = x_12;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_127; uint8_t x_128; 
x_7 = lean_unsigned_to_nat(8192u);
x_8 = lean_unsigned_to_nat(0u);
x_97 = lean_array_get_size(x_1);
x_98 = lean_ctor_get(x_4, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_4, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_4, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_4, 3);
lean_inc(x_101);
x_127 = lean_ctor_get(x_4, 4);
lean_inc(x_127);
x_128 = lean_nat_dec_le(x_7, x_127);
if (x_128 == 0)
{
lean_dec(x_127);
x_102 = x_7;
goto block_126;
}
else
{
x_102 = x_127;
goto block_126;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_mk_empty_array_with_capacity(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_52:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = l_Lean_compiler_enableNew;
x_23 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
x_9 = x_20;
goto block_12;
}
else
{
if (x_13 == 0)
{
lean_object* x_24; 
lean_inc(x_19);
lean_inc(x_18);
x_24 = l_Lean_IR_toIR(x_14, x_18, x_19, x_20);
lean_dec(x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_19, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_25);
x_31 = lean_ir_compile(x_30, x_21, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = lean_array_size(x_32);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___redArg(x_32, x_35, x_15, x_34, x_17, x_18, x_19, x_29);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_dec(x_25);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_ctor_set_tag(x_33, 3);
x_39 = l_Lean_MessageData_ofFormat(x_33);
x_40 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_39, x_16, x_17, x_18, x_19, x_37);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_MessageData_ofFormat(x_42);
x_44 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_43, x_16, x_17, x_18, x_19, x_37);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_dec(x_33);
x_47 = l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___redArg(x_46, x_19, x_45);
lean_dec(x_19);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_25);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_25);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_24;
}
}
else
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
x_9 = x_20;
goto block_12;
}
}
}
block_96:
{
uint8_t x_56; 
x_56 = l_Array_isEmpty___redArg(x_54);
if (x_56 == 0)
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = lean_array_size(x_54);
x_58 = lean_usize_of_nat(x_8);
lean_inc(x_5);
lean_inc(x_53);
lean_inc(x_3);
lean_inc(x_2);
x_59 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__4(x_57, x_58, x_54, x_2, x_3, x_53, x_5, x_55);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Compiler_LCNF_getPassManager(x_53, x_5, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Compiler_LCNF_markRecDecls(x_60);
x_66 = lean_array_size(x_63);
lean_inc(x_5);
lean_inc(x_53);
lean_inc(x_3);
lean_inc(x_2);
x_67 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5(x_63, x_66, x_58, x_65, x_2, x_3, x_53, x_5, x_64);
lean_dec(x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_mk_string_unchecked("Compiler", 8, 8);
x_71 = lean_mk_string_unchecked("result", 6, 6);
x_72 = l_Lean_Name_mkStr2(x_70, x_71);
x_73 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_UnreachableBranches_elimDead_go_spec__0___redArg(x_72, x_53, x_69);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_13 = x_56;
x_14 = x_68;
x_15 = x_58;
x_16 = x_2;
x_17 = x_3;
x_18 = x_53;
x_19 = x_5;
x_20 = x_76;
goto block_52;
}
else
{
lean_object* x_77; lean_object* x_78; size_t x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_array_size(x_68);
lean_inc(x_5);
lean_inc(x_53);
lean_inc(x_3);
lean_inc(x_2);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8(x_68, x_79, x_58, x_78, x_2, x_3, x_53, x_5, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_13 = x_56;
x_14 = x_68;
x_15 = x_58;
x_16 = x_2;
x_17 = x_3;
x_18 = x_53;
x_19 = x_5;
x_20 = x_81;
goto block_52;
}
else
{
uint8_t x_82; 
lean_dec(x_68);
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_80, 0);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_80);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_67);
if (x_86 == 0)
{
return x_67;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_67, 0);
x_88 = lean_ctor_get(x_67, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_67);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_59);
if (x_90 == 0)
{
return x_59;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_59, 0);
x_92 = lean_ctor_get(x_59, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_59);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_mk_empty_array_with_capacity(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_55);
return x_95;
}
}
block_126:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_103 = lean_ctor_get(x_4, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_4, 6);
lean_inc(x_104);
x_105 = lean_ctor_get(x_4, 7);
lean_inc(x_105);
x_106 = lean_ctor_get(x_4, 8);
lean_inc(x_106);
x_107 = lean_ctor_get(x_4, 9);
lean_inc(x_107);
x_108 = lean_ctor_get(x_4, 10);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_110 = lean_ctor_get(x_4, 11);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_112 = lean_ctor_get(x_4, 12);
lean_inc(x_112);
lean_dec(x_4);
x_113 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_113, 0, x_98);
lean_ctor_set(x_113, 1, x_99);
lean_ctor_set(x_113, 2, x_100);
lean_ctor_set(x_113, 3, x_101);
lean_ctor_set(x_113, 4, x_102);
lean_ctor_set(x_113, 5, x_103);
lean_ctor_set(x_113, 6, x_104);
lean_ctor_set(x_113, 7, x_105);
lean_ctor_set(x_113, 8, x_106);
lean_ctor_set(x_113, 9, x_107);
lean_ctor_set(x_113, 10, x_108);
lean_ctor_set(x_113, 11, x_110);
lean_ctor_set(x_113, 12, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*13, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*13 + 1, x_111);
x_114 = lean_mk_empty_array_with_capacity(x_8);
x_115 = lean_nat_dec_lt(x_8, x_97);
if (x_115 == 0)
{
lean_dec(x_97);
x_53 = x_113;
x_54 = x_114;
x_55 = x_6;
goto block_96;
}
else
{
uint8_t x_116; 
x_116 = lean_nat_dec_le(x_97, x_97);
if (x_116 == 0)
{
lean_dec(x_97);
x_53 = x_113;
x_54 = x_114;
x_55 = x_6;
goto block_96;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
x_117 = lean_usize_of_nat(x_8);
x_118 = lean_usize_of_nat(x_97);
lean_dec(x_97);
lean_inc(x_5);
lean_inc(x_113);
x_119 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___redArg(x_1, x_117, x_118, x_114, x_113, x_5, x_6);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_53 = x_113;
x_54 = x_120;
x_55 = x_121;
goto block_96;
}
else
{
uint8_t x_122; 
lean_dec(x_113);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
return x_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_119);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_withTraceNode___at___Lean_Compiler_LCNF_PassManager_run_spec__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_PassManager_run_spec__4(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___lam__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__5(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___redArg(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__6(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at___Lean_Compiler_LCNF_PassManager_run_spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8_spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_PassManager_run_spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_PassManager_run_spec__10(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PassManager_run(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassManager_run___boxed), 6, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_unsigned_to_nat(8u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_6, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
lean_inc_n(x_15, 2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_5, x_18, x_20, x_2, x_3, x_4);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Compiler_LCNF_getDeclAt_x3f___redArg(x_2, x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_mk_string_unchecked("<not-available>", 15, 15);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_mk_string_unchecked("<not-available>", 15, 15);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = l_Lean_Compiler_LCNF_ppDecl_x27(x_17, x_3, x_4, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_showDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Compiler_LCNF_showDecl(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_mk_string_unchecked("compiling new: ", 15, 15);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PassManager_run(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* lean_lcnf_compile_decls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_main___lam__0___boxed), 5, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_mk_string_unchecked("compilation new", 15, 15);
x_8 = lean_mk_string_unchecked("Compiler", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_array_mk(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_main___lam__1___boxed), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(8u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_shiftl(x_13, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_div(x_16, x_17);
lean_dec(x_16);
x_19 = l_Nat_nextPowerOfTwo(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
lean_inc_n(x_22, 2);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CompilerM_run___boxed), 7, 4);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_12);
lean_closure_set(x_27, 2, x_25);
lean_closure_set(x_27, 3, x_26);
x_28 = lean_box(1);
x_29 = lean_mk_string_unchecked("", 0, 0);
x_30 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__20___boxed), 9, 6);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_9);
lean_closure_set(x_30, 2, x_5);
lean_closure_set(x_30, 3, x_27);
lean_closure_set(x_30, 4, x_28);
lean_closure_set(x_30, 5, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_7, x_6, x_30, x_31, x_2, x_3, x_4);
lean_dec(x_6);
lean_dec(x_7);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_main___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_main___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_main___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1699_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("init", 4, 4);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("LCNF", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
lean_inc(x_2);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("Main", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(1699u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
lean_inc(x_24);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("test", 4, 4);
lean_inc(x_2);
x_29 = l_Lean_Name_mkStr2(x_2, x_28);
x_30 = lean_unbox(x_5);
lean_inc(x_24);
x_31 = l_Lean_registerTraceClass(x_29, x_30, x_24, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked("result", 6, 6);
lean_inc(x_2);
x_34 = l_Lean_Name_mkStr2(x_2, x_33);
x_35 = lean_unbox(x_5);
lean_inc(x_24);
x_36 = l_Lean_registerTraceClass(x_34, x_35, x_24, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked("jp", 2, 2);
x_39 = l_Lean_Name_mkStr2(x_2, x_38);
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
x_42 = l_Lean_registerTraceClass(x_39, x_41, x_24, x_37);
return x_42;
}
else
{
lean_dec(x_24);
lean_dec(x_2);
return x_36;
}
}
else
{
lean_dec(x_24);
lean_dec(x_2);
return x_31;
}
}
else
{
lean_dec(x_24);
lean_dec(x_2);
return x_26;
}
}
}
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Checker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Passes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CSE(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Main___hyg_1699_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
