// Lean compiler output
// Module: Lean.Compiler.LCNF.JoinPoints
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PullFunDecls Lean.Compiler.LCNF.FVarUtil Lean.Compiler.LCNF.ScopeM Lean.Compiler.LCNF.InferType
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
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instBEqFVarId;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(lean_object*, lean_object*);
extern lean_object* l_Lean_instFVarIdSetInhabited;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extendJoinPointContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_find_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__1(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__5(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4936_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__10(size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshJpName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__10___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findJoinPoints;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableFVarId;
lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5087_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_commonJoinPointArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5019_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__11(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LCtx_toLocalContext_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5005_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__9___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__12(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__6(size_t, size_t, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = lean_box(0);
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_array_get_size(x_9);
x_11 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_sub(x_21, x_23);
x_25 = lean_usize_land(x_20, x_24);
x_26 = lean_array_uget(x_9, x_25);
lean_dec(x_9);
x_27 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_26);
lean_dec(x_26);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; lean_object* x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_array_get_size(x_29);
x_31 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_32 = lean_unsigned_to_nat(32u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_unsigned_to_nat(16u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_usize_of_nat(x_42);
x_44 = lean_usize_sub(x_41, x_43);
x_45 = lean_usize_land(x_40, x_44);
x_46 = lean_array_uget(x_29, x_45);
lean_dec(x_29);
x_47 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_28);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg(x_1, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 2);
x_14 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_1 = x_15;
x_2 = x_13;
x_10 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
x_15 = lean_box(0);
x_16 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__0(x_15, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
x_4 = x_17;
x_12 = x_18;
goto _start;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg(x_1, x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; lean_object* x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_st_ref_take(x_3, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_55 = lean_ctor_get(x_21, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_array_get_size(x_57);
x_59 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
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
x_75 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec(x_57);
lean_dec(x_56);
x_24 = x_55;
goto block_54;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_55);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_55, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_55, 0);
lean_dec(x_78);
x_79 = lean_box(0);
x_80 = lean_array_uset(x_57, x_73, x_79);
x_81 = lean_nat_sub(x_56, x_70);
lean_dec(x_56);
x_82 = l_Std_DHashMap_Internal_AssocList_erase___at___Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(x_1, x_74);
x_83 = lean_array_uset(x_80, x_73, x_82);
lean_ctor_set(x_55, 1, x_83);
lean_ctor_set(x_55, 0, x_81);
x_24 = x_55;
goto block_54;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_55);
x_84 = lean_box(0);
x_85 = lean_array_uset(x_57, x_73, x_84);
x_86 = lean_nat_sub(x_56, x_70);
lean_dec(x_56);
x_87 = l_Std_DHashMap_Internal_AssocList_erase___at___Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(x_1, x_74);
x_88 = lean_array_uset(x_85, x_73, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_24 = x_89;
goto block_54;
}
}
block_54:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
if (lean_is_scalar(x_23)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_23;
}
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_st_ref_set(x_3, x_26, x_22);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_32);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_33, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
lean_free_object(x_27);
x_38 = lean_usize_of_nat(x_33);
x_39 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_40 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__1(x_32, x_38, x_39, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_32);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_dec(x_19);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_43);
x_46 = lean_box(0);
x_47 = lean_nat_dec_lt(x_44, x_45);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_45, x_45);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_45);
lean_dec(x_43);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; 
x_51 = lean_usize_of_nat(x_44);
x_52 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_53 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__1(x_43, x_51, x_52, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_43);
return x_53;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate_spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_4, 0, x_9);
x_11 = lean_st_ref_set(x_2, x_4, x_7);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_apply_1(x_1, x_20);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_st_ref_set(x_2, x_23, x_19);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___redArg(x_1, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_14 = l_instMonadEIO(lean_box(0));
x_15 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
lean_inc(x_29);
lean_inc(x_26);
lean_inc(x_23);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_23);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_26);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_29);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_10);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
x_46 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_45);
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
x_48 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_47);
x_49 = lean_box(0);
x_50 = l_instInhabitedOfMonad___redArg(x_48, x_49);
x_51 = lean_panic_fn(x_50, x_1);
x_52 = lean_apply_8(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_52;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0(x_1, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_16;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_14 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_15 = lean_unsigned_to_nat(43u);
x_16 = lean_unsigned_to_nat(38u);
x_17 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_18 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_19 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0_spec__0(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_22 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_21;
x_10 = x_23;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_22;
}
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_29 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0___lam__0(x_1, x_25, x_26, x_27, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_25);
return x_29;
}
case 7:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_34 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0___lam__0(x_1, x_30, x_31, x_32, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_30);
return x_34;
}
case 8:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_36 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_37 = lean_unsigned_to_nat(43u);
x_38 = lean_unsigned_to_nat(38u);
x_39 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_40 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
x_41 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0_spec__0(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_41;
}
case 11:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_43 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_44 = lean_unsigned_to_nat(43u);
x_45 = lean_unsigned_to_nat(38u);
x_46 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_47 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_42, x_43, x_44, x_45, x_46);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_42);
x_48 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0_spec__0(x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_48;
}
default: 
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_10);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_9(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___boxed), 9, 0);
x_11 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg_spec__0(x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_17;
x_13 = x_18;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_13);
x_16 = lean_box(0);
x_17 = lean_nat_dec_lt(x_14, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_14);
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0_spec__0(x_1, x_13, x_21, x_22, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
return x_23;
}
}
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = lean_apply_9(x_1, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_25);
x_32 = lean_box(0);
x_33 = lean_nat_dec_lt(x_30, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_31, x_31);
if (x_34 == 0)
{
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
lean_free_object(x_26);
x_35 = lean_usize_of_nat(x_30);
x_36 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_37 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0_spec__0(x_1, x_25, x_35, x_36, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_25);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_array_get_size(x_25);
x_41 = lean_box(0);
x_42 = lean_nat_dec_lt(x_39, x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_40, x_40);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_40);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; 
x_46 = lean_usize_of_nat(x_39);
x_47 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_48 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0_spec__0(x_1, x_25, x_46, x_47, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_25);
return x_48;
}
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_26;
}
}
default: 
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_10);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___boxed), 9, 0);
x_11 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at_____private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue_spec__0_spec__0(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_get_size(x_8);
x_10 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_8, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_25);
x_29 = lean_array_uset(x_8, x_24, x_28);
x_30 = lean_nat_shiftl(x_27, x_3);
x_31 = lean_nat_div(x_30, x_4);
lean_dec(x_30);
x_32 = lean_array_get_size(x_29);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_29);
lean_ctor_set(x_5, 1, x_34);
lean_ctor_set(x_5, 0, x_27);
return x_5;
}
else
{
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_27);
return x_5;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_box(0);
x_36 = lean_array_uset(x_8, x_24, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_2, x_25);
x_38 = lean_array_uset(x_36, x_24, x_37);
lean_ctor_set(x_5, 1, x_38);
return x_5;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; size_t x_51; size_t x_52; lean_object* x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; uint8_t x_58; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
x_41 = lean_array_get_size(x_40);
x_42 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
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
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_usize_of_nat(x_53);
x_55 = lean_usize_sub(x_52, x_54);
x_56 = lean_usize_land(x_51, x_55);
x_57 = lean_array_uget(x_40, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_nat_add(x_39, x_53);
lean_dec(x_39);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_2);
lean_ctor_set(x_60, 2, x_57);
x_61 = lean_array_uset(x_40, x_56, x_60);
x_62 = lean_nat_shiftl(x_59, x_3);
x_63 = lean_nat_div(x_62, x_4);
lean_dec(x_62);
x_64 = lean_array_get_size(x_61);
x_65 = lean_nat_dec_le(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_61);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_box(0);
x_70 = lean_array_uset(x_40, x_56, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_2, x_57);
x_72 = lean_array_uset(x_70, x_56, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_39);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_shiftl(x_5, x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_nextPowerOfTwo(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_7);
lean_closure_set(x_16, 3, x_9);
x_17 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___redArg(x_16, x_3, x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg(x_1, x_2, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_85; uint64_t x_86; lean_object* x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; lean_object* x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; size_t x_95; size_t x_96; lean_object* x_97; size_t x_98; size_t x_99; size_t x_100; lean_object* x_101; uint8_t x_102; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_85 = lean_array_get_size(x_7);
x_86 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_3);
x_87 = lean_unsigned_to_nat(32u);
x_88 = lean_uint64_of_nat(x_87);
x_89 = lean_uint64_shift_right(x_86, x_88);
x_90 = lean_uint64_xor(x_86, x_89);
x_91 = lean_unsigned_to_nat(16u);
x_92 = lean_uint64_of_nat(x_91);
x_93 = lean_uint64_shift_right(x_90, x_92);
x_94 = lean_uint64_xor(x_90, x_93);
x_95 = lean_uint64_to_usize(x_94);
x_96 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_usize_of_nat(x_97);
x_99 = lean_usize_sub(x_96, x_98);
x_100 = lean_usize_land(x_95, x_99);
x_101 = lean_array_uget(x_7, x_100);
x_102 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_3, x_101);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_5);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_104 = lean_ctor_get(x_5, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_5, 0);
lean_dec(x_105);
x_106 = lean_box(0);
x_107 = lean_nat_add(x_6, x_97);
lean_dec(x_6);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_3);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_101);
x_109 = lean_array_uset(x_7, x_100, x_108);
x_110 = lean_unsigned_to_nat(2u);
x_111 = lean_nat_shiftl(x_107, x_110);
x_112 = lean_unsigned_to_nat(3u);
x_113 = lean_nat_div(x_111, x_112);
lean_dec(x_111);
x_114 = lean_array_get_size(x_109);
x_115 = lean_nat_dec_le(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_109);
lean_ctor_set(x_5, 1, x_116);
lean_ctor_set(x_5, 0, x_107);
x_9 = x_5;
goto block_84;
}
else
{
lean_ctor_set(x_5, 1, x_109);
lean_ctor_set(x_5, 0, x_107);
x_9 = x_5;
goto block_84;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_5);
x_117 = lean_box(0);
x_118 = lean_nat_add(x_6, x_97);
lean_dec(x_6);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_3);
lean_ctor_set(x_119, 1, x_117);
lean_ctor_set(x_119, 2, x_101);
x_120 = lean_array_uset(x_7, x_100, x_119);
x_121 = lean_unsigned_to_nat(2u);
x_122 = lean_nat_shiftl(x_118, x_121);
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_nat_div(x_122, x_123);
lean_dec(x_122);
x_125 = lean_array_get_size(x_120);
x_126 = lean_nat_dec_le(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_120);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_118);
lean_ctor_set(x_128, 1, x_127);
x_9 = x_128;
goto block_84;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_120);
x_9 = x_129;
goto block_84;
}
}
}
else
{
lean_dec(x_101);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_9 = x_5;
goto block_84;
}
block_84:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_array_get_size(x_12);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
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
x_30 = lean_array_uget(x_12, x_29);
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_2, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_nat_add(x_11, x_26);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_13);
lean_ctor_set(x_33, 2, x_30);
x_34 = lean_array_uset(x_12, x_29, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_shiftl(x_32, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_34);
lean_ctor_set(x_4, 1, x_41);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_ctor_set(x_4, 1, x_34);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_box(0);
x_43 = lean_array_uset(x_12, x_29, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_2, x_13, x_30);
x_45 = lean_array_uset(x_43, x_29, x_44);
lean_ctor_set(x_4, 1, x_45);
return x_4;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; size_t x_59; size_t x_60; lean_object* x_61; size_t x_62; size_t x_63; size_t x_64; lean_object* x_65; uint8_t x_66; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_9);
x_49 = lean_array_get_size(x_47);
x_50 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
x_51 = lean_unsigned_to_nat(32u);
x_52 = lean_uint64_of_nat(x_51);
x_53 = lean_uint64_shift_right(x_50, x_52);
x_54 = lean_uint64_xor(x_50, x_53);
x_55 = lean_unsigned_to_nat(16u);
x_56 = lean_uint64_of_nat(x_55);
x_57 = lean_uint64_shift_right(x_54, x_56);
x_58 = lean_uint64_xor(x_54, x_57);
x_59 = lean_uint64_to_usize(x_58);
x_60 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_usize_of_nat(x_61);
x_63 = lean_usize_sub(x_60, x_62);
x_64 = lean_usize_land(x_59, x_63);
x_65 = lean_array_uget(x_47, x_64);
x_66 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_2, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_nat_add(x_46, x_61);
lean_dec(x_46);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_2);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_65);
x_69 = lean_array_uset(x_47, x_64, x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_shiftl(x_67, x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_nat_div(x_71, x_72);
lean_dec(x_71);
x_74 = lean_array_get_size(x_69);
x_75 = lean_nat_dec_le(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_69);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_69);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_box(0);
x_80 = lean_array_uset(x_47, x_64, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_2, x_48, x_65);
x_82 = lean_array_uset(x_80, x_64, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_46);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg(x_2, x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___lam__0), 4, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_1);
x_18 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___redArg(x_17, x_4, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_9(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_9(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(x_4, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2___redArg___lam__0), 9, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2_spec__2___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_find_go), 9, 0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__0(x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
x_4 = x_17;
x_12 = x_18;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 5)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_10, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 4)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_80; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_28);
x_80 = lean_nat_dec_lt(x_29, x_30);
if (x_80 == 0)
{
lean_dec(x_28);
x_31 = x_9;
goto block_79;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_30, x_30);
if (x_81 == 0)
{
lean_dec(x_28);
x_31 = x_9;
goto block_79;
}
else
{
lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; 
x_82 = lean_box(0);
x_83 = lean_usize_of_nat(x_29);
x_84 = lean_usize_of_nat(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_85 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__1(x_28, x_83, x_84, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_28);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_31 = x_86;
goto block_79;
}
else
{
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_85;
}
}
}
block_79:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___redArg(x_27, x_3, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_10);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_27);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_32, 1);
x_38 = lean_ctor_get(x_32, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
lean_dec(x_10);
x_41 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_26, x_40);
lean_dec(x_40);
lean_dec(x_26);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_free_object(x_32);
lean_dec(x_30);
x_42 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_27);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_nat_dec_eq(x_30, x_43);
lean_dec(x_43);
lean_dec(x_30);
if (x_44 == 0)
{
lean_object* x_45; 
lean_free_object(x_32);
x_45 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_27);
return x_45;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_46; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_box(0);
lean_ctor_set(x_32, 0, x_46);
return x_32;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_free_object(x_32);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(x_27, x_4, x_37);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_27, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_48, 0, x_55);
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_dec(x_48);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_32, 1);
lean_inc(x_59);
lean_dec(x_32);
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
lean_dec(x_10);
x_62 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_26, x_61);
lean_dec(x_61);
lean_dec(x_26);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_30);
x_63 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_27);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_nat_dec_eq(x_30, x_64);
lean_dec(x_64);
lean_dec(x_30);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_27);
return x_66;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
x_70 = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(x_27, x_4, x_59);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_27, x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_69);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
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
lean_dec(x_25);
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
goto block_24;
}
}
else
{
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
goto block_24;
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_10, 3);
lean_inc(x_20);
lean_dec(x_10);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_21 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue(x_20, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_1 = x_11;
x_2 = x_12;
x_3 = x_13;
x_4 = x_14;
x_5 = x_15;
x_6 = x_16;
x_7 = x_17;
x_8 = x_18;
x_9 = x_22;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_21;
}
}
}
case 1:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
lean_dec(x_1);
x_89 = lean_ctor_get(x_87, 4);
lean_inc(x_89);
x_90 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_find_go), 9, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
lean_inc(x_91);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_93 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__2___redArg(x_90, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lean_Compiler_LCNF_FunDeclCore_getArity___redArg(x_87);
lean_dec(x_87);
lean_inc(x_91);
x_96 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___redArg(x_91, x_95, x_3, x_94);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(x_91, x_4, x_97);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_1 = x_88;
x_9 = x_99;
goto _start;
}
else
{
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_93;
}
}
case 2:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_1, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_1, 1);
lean_inc(x_102);
lean_dec(x_1);
x_103 = lean_ctor_get(x_101, 4);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_104 = l_Lean_Compiler_LCNF_JoinPointFinder_find_go(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_1 = x_102;
x_9 = x_105;
goto _start;
}
else
{
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_104;
}
}
case 3:
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_1);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_108 = lean_ctor_get(x_1, 1);
x_109 = lean_ctor_get(x_1, 0);
lean_dec(x_109);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_array_get_size(x_108);
x_112 = lean_box(0);
x_113 = lean_nat_dec_lt(x_110, x_111);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_112);
return x_1;
}
else
{
uint8_t x_114; 
x_114 = lean_nat_dec_le(x_111, x_111);
if (x_114 == 0)
{
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_112);
return x_1;
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
lean_free_object(x_1);
x_115 = lean_usize_of_nat(x_110);
x_116 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_117 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__1(x_108, x_115, x_116, x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_108);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
lean_dec(x_1);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_array_get_size(x_118);
x_121 = lean_box(0);
x_122 = lean_nat_dec_lt(x_119, x_120);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_9);
return x_123;
}
else
{
uint8_t x_124; 
x_124 = lean_nat_dec_le(x_120, x_120);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_9);
return x_125;
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; 
x_126 = lean_usize_of_nat(x_119);
x_127 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_128 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__1(x_118, x_126, x_127, x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_118);
return x_128;
}
}
}
}
case 4:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
lean_dec(x_1);
x_130 = lean_ctor_get(x_129, 2);
lean_inc(x_130);
x_131 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_130, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_130);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_133 = lean_ctor_get(x_131, 1);
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
x_135 = lean_ctor_get(x_129, 3);
lean_inc(x_135);
lean_dec(x_129);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_array_get_size(x_135);
x_138 = lean_box(0);
x_139 = lean_nat_dec_lt(x_136, x_137);
if (x_139 == 0)
{
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_131, 0, x_138);
return x_131;
}
else
{
uint8_t x_140; 
x_140 = lean_nat_dec_le(x_137, x_137);
if (x_140 == 0)
{
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_131, 0, x_138);
return x_131;
}
else
{
size_t x_141; size_t x_142; lean_object* x_143; 
lean_free_object(x_131);
x_141 = lean_usize_of_nat(x_136);
x_142 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_143 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__4(x_135, x_141, x_142, x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_133);
lean_dec(x_135);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_131, 1);
lean_inc(x_144);
lean_dec(x_131);
x_145 = lean_ctor_get(x_129, 3);
lean_inc(x_145);
lean_dec(x_129);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_array_get_size(x_145);
x_148 = lean_box(0);
x_149 = lean_nat_dec_lt(x_146, x_147);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_144);
return x_150;
}
else
{
uint8_t x_151; 
x_151 = lean_nat_dec_le(x_147, x_147);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_144);
return x_152;
}
else
{
size_t x_153; size_t x_154; lean_object* x_155; 
x_153 = lean_usize_of_nat(x_146);
x_154 = lean_usize_of_nat(x_147);
lean_dec(x_147);
x_155 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__4(x_145, x_153, x_154, x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_144);
lean_dec(x_145);
return x_155;
}
}
}
}
case 5:
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_1, 0);
lean_inc(x_156);
lean_dec(x_1);
x_157 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_156);
return x_157;
}
default: 
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_9);
return x_159;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_find_go_spec__4(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_find_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_unsigned_to_nat(8u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_7, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_st_mk_ref(x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_mk_array(x_12, x_13);
lean_ctor_set(x_15, 1, x_20);
lean_ctor_set(x_15, 0, x_19);
lean_inc(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_15);
x_22 = lean_st_mk_ref(x_21, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_find_go), 9, 0);
x_26 = lean_ctor_get(x_1, 4);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_box(0);
lean_inc(x_17);
lean_inc(x_23);
x_28 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_find_spec__0(x_25, x_26, x_27, x_23, x_17, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_23, x_29);
lean_dec(x_23);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_17, x_32);
lean_dec(x_17);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_23);
lean_dec(x_17);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_mk_array(x_12, x_13);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_st_mk_ref(x_47, x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_find_go), 9, 0);
x_52 = lean_ctor_get(x_1, 4);
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_box(0);
lean_inc(x_42);
lean_inc(x_49);
x_54 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_find_spec__0(x_51, x_52, x_53, x_49, x_42, x_2, x_3, x_4, x_5, x_50);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_get(x_49, x_55);
lean_dec(x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_42, x_58);
lean_dec(x_42);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_49);
lean_dec(x_42);
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_9 = x_23;
goto block_22;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_9 = x_24;
goto block_22;
}
block_22:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_replace_go), 7, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__0(x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_18, x_2, x_15);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_8, 3);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
lean_dec(x_9);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
x_42 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_37, x_41);
lean_dec(x_41);
lean_dec(x_37);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set_tag(x_36, 0);
lean_ctor_set(x_36, 1, x_7);
lean_ctor_set(x_36, 0, x_1);
return x_36;
}
else
{
uint8_t x_43; 
lean_free_object(x_36);
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; size_t x_56; size_t x_57; lean_object* x_58; size_t x_59; size_t x_60; size_t x_61; lean_object* x_62; uint8_t x_63; 
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_46 = lean_array_get_size(x_44);
x_47 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_39);
x_48 = lean_unsigned_to_nat(32u);
x_49 = lean_uint64_of_nat(x_48);
x_50 = lean_uint64_shift_right(x_47, x_49);
x_51 = lean_uint64_xor(x_47, x_50);
x_52 = lean_unsigned_to_nat(16u);
x_53 = lean_uint64_of_nat(x_52);
x_54 = lean_uint64_shift_right(x_51, x_53);
x_55 = lean_uint64_xor(x_51, x_54);
x_56 = lean_uint64_to_usize(x_55);
x_57 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_usize_of_nat(x_58);
x_60 = lean_usize_sub(x_57, x_59);
x_61 = lean_usize_land(x_56, x_60);
x_62 = lean_array_uget(x_44, x_61);
lean_dec(x_44);
x_63 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_39, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
uint8_t x_64; 
lean_free_object(x_2);
x_64 = !lean_is_exclusive(x_1);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_1, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_1, 0);
lean_dec(x_66);
x_67 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_8, x_4, x_7);
lean_dec(x_4);
lean_dec(x_8);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set(x_67, 0, x_1);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_39);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_72 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_8, x_4, x_7);
lean_dec(x_4);
lean_dec(x_8);
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
x_75 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_75, 0, x_39);
lean_ctor_set(x_75, 1, x_40);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; lean_object* x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; size_t x_88; size_t x_89; lean_object* x_90; size_t x_91; size_t x_92; size_t x_93; lean_object* x_94; uint8_t x_95; 
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
lean_dec(x_2);
x_78 = lean_array_get_size(x_77);
x_79 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_39);
x_80 = lean_unsigned_to_nat(32u);
x_81 = lean_uint64_of_nat(x_80);
x_82 = lean_uint64_shift_right(x_79, x_81);
x_83 = lean_uint64_xor(x_79, x_82);
x_84 = lean_unsigned_to_nat(16u);
x_85 = lean_uint64_of_nat(x_84);
x_86 = lean_uint64_shift_right(x_83, x_85);
x_87 = lean_uint64_xor(x_83, x_86);
x_88 = lean_uint64_to_usize(x_87);
x_89 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_usize_of_nat(x_90);
x_92 = lean_usize_sub(x_89, x_91);
x_93 = lean_usize_land(x_88, x_92);
x_94 = lean_array_uget(x_77, x_93);
lean_dec(x_77);
x_95 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_39, x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_4);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_7);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_97 = x_1;
} else {
 lean_dec_ref(x_1);
 x_97 = lean_box(0);
}
x_98 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_8, x_4, x_7);
lean_dec(x_4);
lean_dec(x_8);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(3, 2, 0);
} else {
 x_101 = x_97;
 lean_ctor_set_tag(x_101, 3);
}
lean_ctor_set(x_101, 0, x_39);
lean_ctor_set(x_101, 1, x_40);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_36, 0);
x_104 = lean_ctor_get(x_36, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_36);
x_105 = lean_ctor_get(x_8, 0);
lean_inc(x_105);
x_106 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_37, x_105);
lean_dec(x_105);
lean_dec(x_37);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_7);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; lean_object* x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; size_t x_120; size_t x_121; lean_object* x_122; size_t x_123; size_t x_124; size_t x_125; lean_object* x_126; uint8_t x_127; 
x_108 = lean_ctor_get(x_2, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_109 = x_2;
} else {
 lean_dec_ref(x_2);
 x_109 = lean_box(0);
}
x_110 = lean_array_get_size(x_108);
x_111 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_103);
x_112 = lean_unsigned_to_nat(32u);
x_113 = lean_uint64_of_nat(x_112);
x_114 = lean_uint64_shift_right(x_111, x_113);
x_115 = lean_uint64_xor(x_111, x_114);
x_116 = lean_unsigned_to_nat(16u);
x_117 = lean_uint64_of_nat(x_116);
x_118 = lean_uint64_shift_right(x_115, x_117);
x_119 = lean_uint64_xor(x_115, x_118);
x_120 = lean_uint64_to_usize(x_119);
x_121 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_usize_of_nat(x_122);
x_124 = lean_usize_sub(x_121, x_123);
x_125 = lean_usize_land(x_120, x_124);
x_126 = lean_array_uget(x_108, x_125);
lean_dec(x_108);
x_127 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_103, x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_8);
lean_dec(x_4);
if (lean_is_scalar(x_109)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_109;
}
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_7);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_109);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_129 = x_1;
} else {
 lean_dec_ref(x_1);
 x_129 = lean_box(0);
}
x_130 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_8, x_4, x_7);
lean_dec(x_4);
lean_dec(x_8);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_133 = lean_alloc_ctor(3, 2, 0);
} else {
 x_133 = x_129;
 lean_ctor_set_tag(x_133, 3);
}
lean_ctor_set(x_133, 0, x_103);
lean_ctor_set(x_133, 1, x_104);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
}
}
else
{
lean_dec(x_36);
x_21 = x_2;
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
goto block_35;
}
}
else
{
x_21 = x_2;
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
goto block_35;
}
block_20:
{
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
block_35:
{
lean_object* x_27; 
lean_inc(x_9);
x_27 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_9, x_21, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_31 = lean_ptr_addr(x_28);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
x_10 = x_28;
x_11 = x_29;
x_12 = x_32;
goto block_20;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_8);
x_34 = lean_usize_dec_eq(x_33, x_33);
x_10 = x_28;
x_11 = x_29;
x_12 = x_34;
goto block_20;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_27;
}
}
}
case 1:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint64_t x_140; lean_object* x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; lean_object* x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; size_t x_149; size_t x_150; lean_object* x_151; size_t x_152; size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; 
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
x_139 = lean_array_get_size(x_137);
x_140 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_138);
x_141 = lean_unsigned_to_nat(32u);
x_142 = lean_uint64_of_nat(x_141);
x_143 = lean_uint64_shift_right(x_140, x_142);
x_144 = lean_uint64_xor(x_140, x_143);
x_145 = lean_unsigned_to_nat(16u);
x_146 = lean_uint64_of_nat(x_145);
x_147 = lean_uint64_shift_right(x_144, x_146);
x_148 = lean_uint64_xor(x_144, x_147);
x_149 = lean_uint64_to_usize(x_148);
x_150 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_usize_of_nat(x_151);
x_153 = lean_usize_sub(x_150, x_152);
x_154 = lean_usize_land(x_149, x_153);
x_155 = lean_array_uget(x_137, x_154);
lean_dec(x_137);
x_156 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_138, x_155);
lean_dec(x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_138);
x_157 = lean_ctor_get(x_135, 4);
lean_inc(x_157);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_158 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_157, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_135, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_135, 2);
lean_inc(x_162);
lean_inc(x_135);
x_163 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_135, x_161, x_162, x_159, x_4, x_160);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_136);
x_166 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_136, x_2, x_3, x_4, x_5, x_6, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; size_t x_179; size_t x_180; uint8_t x_181; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_179 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_180 = lean_ptr_addr(x_167);
x_181 = lean_usize_dec_eq(x_179, x_180);
if (x_181 == 0)
{
lean_dec(x_135);
x_170 = x_181;
goto block_178;
}
else
{
size_t x_182; size_t x_183; uint8_t x_184; 
x_182 = lean_ptr_addr(x_135);
lean_dec(x_135);
x_183 = lean_ptr_addr(x_164);
x_184 = lean_usize_dec_eq(x_182, x_183);
x_170 = x_184;
goto block_178;
}
block_178:
{
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_1);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_1, 1);
lean_dec(x_172);
x_173 = lean_ctor_get(x_1, 0);
lean_dec(x_173);
lean_ctor_set(x_1, 1, x_167);
lean_ctor_set(x_1, 0, x_164);
if (lean_is_scalar(x_169)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_169;
}
lean_ctor_set(x_174, 0, x_1);
lean_ctor_set(x_174, 1, x_168);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_1);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_164);
lean_ctor_set(x_175, 1, x_167);
if (lean_is_scalar(x_169)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_169;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_168);
return x_176;
}
}
else
{
lean_object* x_177; 
lean_dec(x_167);
lean_dec(x_164);
if (lean_is_scalar(x_169)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_169;
}
lean_ctor_set(x_177, 0, x_1);
lean_ctor_set(x_177, 1, x_168);
return x_177;
}
}
}
else
{
lean_dec(x_164);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_1);
return x_166;
}
}
else
{
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_158;
}
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_1);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_1, 1);
lean_dec(x_186);
x_187 = lean_ctor_get(x_1, 0);
lean_dec(x_187);
x_188 = lean_ctor_get(x_156, 0);
lean_inc(x_188);
lean_dec(x_156);
x_189 = lean_ctor_get(x_135, 4);
lean_inc(x_189);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_190 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_189, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_st_ref_take(x_4, x_192);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
x_197 = lean_ctor_get(x_135, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_135, 3);
lean_inc(x_198);
lean_dec(x_135);
x_199 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_199, 0, x_138);
lean_ctor_set(x_199, 1, x_188);
lean_ctor_set(x_199, 2, x_197);
lean_ctor_set(x_199, 3, x_198);
lean_ctor_set(x_199, 4, x_191);
x_200 = lean_ctor_get(x_195, 0);
lean_inc(x_200);
lean_inc(x_199);
x_201 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_200, x_199);
x_202 = lean_ctor_get(x_195, 1);
lean_inc(x_202);
lean_dec(x_195);
lean_ctor_set(x_193, 1, x_202);
lean_ctor_set(x_193, 0, x_201);
x_203 = lean_st_ref_set(x_4, x_193, x_196);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_136, x_2, x_3, x_4, x_5, x_6, x_204);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_205, 0);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_207);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set(x_205, 0, x_1);
return x_205;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_205, 0);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_205);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_208);
lean_ctor_set(x_1, 0, x_199);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_1);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
else
{
lean_dec(x_199);
lean_free_object(x_1);
return x_205;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_211 = lean_ctor_get(x_193, 0);
x_212 = lean_ctor_get(x_193, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_193);
x_213 = lean_ctor_get(x_135, 2);
lean_inc(x_213);
x_214 = lean_ctor_get(x_135, 3);
lean_inc(x_214);
lean_dec(x_135);
x_215 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_215, 0, x_138);
lean_ctor_set(x_215, 1, x_188);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_214);
lean_ctor_set(x_215, 4, x_191);
x_216 = lean_ctor_get(x_211, 0);
lean_inc(x_216);
lean_inc(x_215);
x_217 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_216, x_215);
x_218 = lean_ctor_get(x_211, 1);
lean_inc(x_218);
lean_dec(x_211);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_st_ref_set(x_4, x_219, x_212);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_136, x_2, x_3, x_4, x_5, x_6, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_215);
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_1);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
else
{
lean_dec(x_215);
lean_free_object(x_1);
return x_222;
}
}
}
else
{
lean_dec(x_188);
lean_free_object(x_1);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_190;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_1);
x_227 = lean_ctor_get(x_156, 0);
lean_inc(x_227);
lean_dec(x_156);
x_228 = lean_ctor_get(x_135, 4);
lean_inc(x_228);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_229 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_228, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_st_ref_take(x_4, x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_135, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_135, 3);
lean_inc(x_237);
lean_dec(x_135);
x_238 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_238, 0, x_138);
lean_ctor_set(x_238, 1, x_227);
lean_ctor_set(x_238, 2, x_236);
lean_ctor_set(x_238, 3, x_237);
lean_ctor_set(x_238, 4, x_230);
x_239 = lean_ctor_get(x_233, 0);
lean_inc(x_239);
lean_inc(x_238);
x_240 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_239, x_238);
x_241 = lean_ctor_get(x_233, 1);
lean_inc(x_241);
lean_dec(x_233);
if (lean_is_scalar(x_235)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_235;
}
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_st_ref_set(x_4, x_242, x_234);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_136, x_2, x_3, x_4, x_5, x_6, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_248 = x_245;
} else {
 lean_dec_ref(x_245);
 x_248 = lean_box(0);
}
x_249 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_249, 0, x_238);
lean_ctor_set(x_249, 1, x_246);
if (lean_is_scalar(x_248)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_248;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_247);
return x_250;
}
else
{
lean_dec(x_238);
return x_245;
}
}
else
{
lean_dec(x_227);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_229;
}
}
}
}
case 2:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_1, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_1, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 4);
lean_inc(x_253);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_254 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_253, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_251, 3);
lean_inc(x_257);
x_258 = lean_ctor_get(x_251, 2);
lean_inc(x_258);
lean_inc(x_251);
x_259 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_251, x_257, x_258, x_255, x_4, x_256);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
lean_inc(x_252);
x_262 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_252, x_2, x_3, x_4, x_5, x_6, x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; size_t x_275; size_t x_276; uint8_t x_277; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_275 = lean_ptr_addr(x_252);
lean_dec(x_252);
x_276 = lean_ptr_addr(x_263);
x_277 = lean_usize_dec_eq(x_275, x_276);
if (x_277 == 0)
{
lean_dec(x_251);
x_266 = x_277;
goto block_274;
}
else
{
size_t x_278; size_t x_279; uint8_t x_280; 
x_278 = lean_ptr_addr(x_251);
lean_dec(x_251);
x_279 = lean_ptr_addr(x_260);
x_280 = lean_usize_dec_eq(x_278, x_279);
x_266 = x_280;
goto block_274;
}
block_274:
{
if (x_266 == 0)
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_1);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_1, 1);
lean_dec(x_268);
x_269 = lean_ctor_get(x_1, 0);
lean_dec(x_269);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_260);
if (lean_is_scalar(x_265)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_265;
}
lean_ctor_set(x_270, 0, x_1);
lean_ctor_set(x_270, 1, x_264);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_1);
x_271 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_271, 0, x_260);
lean_ctor_set(x_271, 1, x_263);
if (lean_is_scalar(x_265)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_265;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_264);
return x_272;
}
}
else
{
lean_object* x_273; 
lean_dec(x_263);
lean_dec(x_260);
if (lean_is_scalar(x_265)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_265;
}
lean_ctor_set(x_273, 0, x_1);
lean_ctor_set(x_273, 1, x_264);
return x_273;
}
}
}
else
{
lean_dec(x_260);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_1);
return x_262;
}
}
else
{
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_254;
}
}
case 4:
{
lean_object* x_281; lean_object* x_282; size_t x_283; lean_object* x_284; size_t x_285; lean_object* x_286; 
x_281 = lean_ctor_get(x_1, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_281, 3);
lean_inc(x_282);
x_283 = lean_array_size(x_282);
x_284 = lean_unsigned_to_nat(0u);
x_285 = lean_usize_of_nat(x_284);
lean_inc(x_282);
x_286 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__1(x_283, x_285, x_282, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_297; size_t x_301; size_t x_302; uint8_t x_303; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_281, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_281, 2);
lean_inc(x_291);
x_301 = lean_ptr_addr(x_282);
lean_dec(x_282);
x_302 = lean_ptr_addr(x_287);
x_303 = lean_usize_dec_eq(x_301, x_302);
if (x_303 == 0)
{
x_297 = x_303;
goto block_300;
}
else
{
size_t x_304; uint8_t x_305; 
x_304 = lean_ptr_addr(x_290);
x_305 = lean_usize_dec_eq(x_304, x_304);
x_297 = x_305;
goto block_300;
}
block_296:
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_281, 0);
lean_inc(x_292);
lean_dec(x_281);
x_293 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_290);
lean_ctor_set(x_293, 2, x_291);
lean_ctor_set(x_293, 3, x_287);
x_294 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_294, 0, x_293);
if (lean_is_scalar(x_289)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_289;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_288);
return x_295;
}
block_300:
{
if (x_297 == 0)
{
lean_dec(x_1);
goto block_296;
}
else
{
uint8_t x_298; 
x_298 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_291, x_291);
if (x_298 == 0)
{
lean_dec(x_1);
goto block_296;
}
else
{
lean_object* x_299; 
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_287);
lean_dec(x_281);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_1);
lean_ctor_set(x_299, 1, x_288);
return x_299;
}
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_286);
if (x_306 == 0)
{
return x_286;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_286, 0);
x_308 = lean_ctor_get(x_286, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_286);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
default: 
{
lean_object* x_310; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_1);
lean_ctor_set(x_310, 1, x_7);
return x_310;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointFinder_replace_go_spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 1);
lean_dec(x_9);
x_10 = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_array_get_size(x_15);
x_17 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_7);
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
x_32 = lean_array_uget(x_15, x_31);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_7, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_nat_add(x_14, x_28);
lean_dec(x_14);
lean_ctor_set(x_2, 2, x_32);
lean_ctor_set(x_2, 1, x_11);
x_35 = lean_array_uset(x_15, x_31, x_2);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_shiftl(x_34, x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_nat_div(x_37, x_38);
lean_dec(x_37);
x_40 = lean_array_get_size(x_35);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_35);
lean_ctor_set(x_1, 1, x_42);
lean_ctor_set(x_1, 0, x_34);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_35);
lean_ctor_set(x_1, 0, x_34);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_2);
x_45 = lean_box(0);
x_46 = lean_array_uset(x_15, x_31, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_7, x_11, x_32);
x_48 = lean_array_uset(x_46, x_31, x_47);
lean_ctor_set(x_1, 1, x_48);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; lean_object* x_64; size_t x_65; size_t x_66; size_t x_67; lean_object* x_68; uint8_t x_69; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_52 = lean_array_get_size(x_51);
x_53 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_7);
x_54 = lean_unsigned_to_nat(32u);
x_55 = lean_uint64_of_nat(x_54);
x_56 = lean_uint64_shift_right(x_53, x_55);
x_57 = lean_uint64_xor(x_53, x_56);
x_58 = lean_unsigned_to_nat(16u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_shift_right(x_57, x_59);
x_61 = lean_uint64_xor(x_57, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_usize_of_nat(x_64);
x_66 = lean_usize_sub(x_63, x_65);
x_67 = lean_usize_land(x_62, x_66);
x_68 = lean_array_uget(x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_7, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_70 = lean_nat_add(x_50, x_64);
lean_dec(x_50);
lean_ctor_set(x_2, 2, x_68);
lean_ctor_set(x_2, 1, x_11);
x_71 = lean_array_uset(x_51, x_67, x_2);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_nat_shiftl(x_70, x_72);
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
x_78 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_71);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_78);
x_1 = x_79;
x_2 = x_8;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_70);
lean_ctor_set(x_81, 1, x_71);
x_1 = x_81;
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_free_object(x_2);
x_83 = lean_box(0);
x_84 = lean_array_uset(x_51, x_67, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_7, x_11, x_68);
x_86 = lean_array_uset(x_84, x_67, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_50);
lean_ctor_set(x_87, 1, x_86);
x_1 = x_87;
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; lean_object* x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; size_t x_107; size_t x_108; lean_object* x_109; size_t x_110; size_t x_111; size_t x_112; lean_object* x_113; uint8_t x_114; 
x_89 = lean_ctor_get(x_2, 0);
x_90 = lean_ctor_get(x_2, 2);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_2);
x_91 = l_Lean_Compiler_LCNF_mkFreshJpName___redArg(x_3, x_4);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_1, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_96 = x_1;
} else {
 lean_dec_ref(x_1);
 x_96 = lean_box(0);
}
x_97 = lean_array_get_size(x_95);
x_98 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_89);
x_99 = lean_unsigned_to_nat(32u);
x_100 = lean_uint64_of_nat(x_99);
x_101 = lean_uint64_shift_right(x_98, x_100);
x_102 = lean_uint64_xor(x_98, x_101);
x_103 = lean_unsigned_to_nat(16u);
x_104 = lean_uint64_of_nat(x_103);
x_105 = lean_uint64_shift_right(x_102, x_104);
x_106 = lean_uint64_xor(x_102, x_105);
x_107 = lean_uint64_to_usize(x_106);
x_108 = lean_usize_of_nat(x_97);
lean_dec(x_97);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_usize_of_nat(x_109);
x_111 = lean_usize_sub(x_108, x_110);
x_112 = lean_usize_land(x_107, x_111);
x_113 = lean_array_uget(x_95, x_112);
x_114 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_89, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_115 = lean_nat_add(x_94, x_109);
lean_dec(x_94);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_89);
lean_ctor_set(x_116, 1, x_92);
lean_ctor_set(x_116, 2, x_113);
x_117 = lean_array_uset(x_95, x_112, x_116);
x_118 = lean_unsigned_to_nat(2u);
x_119 = lean_nat_shiftl(x_115, x_118);
x_120 = lean_unsigned_to_nat(3u);
x_121 = lean_nat_div(x_119, x_120);
lean_dec(x_119);
x_122 = lean_array_get_size(x_117);
x_123 = lean_nat_dec_le(x_121, x_122);
lean_dec(x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_117);
if (lean_is_scalar(x_96)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_96;
}
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_124);
x_1 = x_125;
x_2 = x_90;
x_4 = x_93;
goto _start;
}
else
{
lean_object* x_127; 
if (lean_is_scalar(x_96)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_96;
}
lean_ctor_set(x_127, 0, x_115);
lean_ctor_set(x_127, 1, x_117);
x_1 = x_127;
x_2 = x_90;
x_4 = x_93;
goto _start;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_box(0);
x_130 = lean_array_uset(x_95, x_112, x_129);
x_131 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_89, x_92, x_113);
x_132 = lean_array_uset(x_130, x_112, x_131);
if (lean_is_scalar(x_96)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_96;
}
lean_ctor_set(x_133, 0, x_94);
lean_ctor_set(x_133, 1, x_132);
x_1 = x_133;
x_2 = x_90;
x_4 = x_93;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
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
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___redArg(x_4, x_11, x_6, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_13;
x_9 = x_14;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_39 = lean_unsigned_to_nat(8u);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_nat_shiftl(x_39, x_41);
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_nat_div(x_42, x_43);
lean_dec(x_42);
x_45 = l_Nat_nextPowerOfTwo(x_44);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_mk_array(x_45, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_ctor_get(x_49, 1);
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_40, x_51);
if (x_52 == 0)
{
lean_dec(x_51);
x_8 = x_48;
x_9 = x_7;
goto block_38;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_51, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
x_8 = x_48;
x_9 = x_7;
goto block_38;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_usize_of_nat(x_40);
x_55 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_56 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__2(x_50, x_54, x_55, x_48, x_3, x_4, x_5, x_6, x_7);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_8 = x_57;
x_9 = x_58;
goto block_38;
}
}
block_38:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_replace_go), 7, 0);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__1(x_10, x_11, x_8, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_21 = lean_ctor_get(x_1, 5);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_14);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*6, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*6 + 1, x_20);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_31 = lean_ctor_get(x_1, 5);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_23);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*6, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*6 + 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointFinder_replace_spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_JoinPointFinder_replace(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_11, x_2);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_12) == 0)
{
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_8);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_st_ref_get(x_3, x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; lean_object* x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_instBEqFVarId;
x_19 = l_Lean_instHashableFVarId;
x_20 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_array_get_size(x_17);
x_22 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_13);
x_23 = lean_unsigned_to_nat(32u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_shift_right(x_22, x_24);
x_26 = lean_uint64_xor(x_22, x_25);
x_27 = lean_unsigned_to_nat(16u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_sub(x_32, x_34);
x_36 = lean_usize_land(x_31, x_35);
x_37 = lean_array_uget(x_17, x_36);
lean_dec(x_17);
x_38 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_20, x_13, x_37);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_array_get_size(x_39);
x_41 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_42 = lean_uint64_shift_right(x_41, x_24);
x_43 = lean_uint64_xor(x_41, x_42);
x_44 = lean_uint64_shift_right(x_43, x_28);
x_45 = lean_uint64_xor(x_43, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_48 = lean_usize_sub(x_47, x_34);
x_49 = lean_usize_land(x_46, x_48);
x_50 = lean_array_uget(x_39, x_49);
lean_dec(x_39);
x_51 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_50);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
lean_ctor_set(x_14, 0, x_53);
return x_14;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; size_t x_70; size_t x_71; lean_object* x_72; size_t x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; size_t x_85; size_t x_86; size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_instBEqFVarId;
x_58 = l_Lean_instHashableFVarId;
x_59 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_57, x_58);
x_60 = lean_array_get_size(x_56);
x_61 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_13);
x_62 = lean_unsigned_to_nat(32u);
x_63 = lean_uint64_of_nat(x_62);
x_64 = lean_uint64_shift_right(x_61, x_63);
x_65 = lean_uint64_xor(x_61, x_64);
x_66 = lean_unsigned_to_nat(16u);
x_67 = lean_uint64_of_nat(x_66);
x_68 = lean_uint64_shift_right(x_65, x_67);
x_69 = lean_uint64_xor(x_65, x_68);
x_70 = lean_uint64_to_usize(x_69);
x_71 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_usize_of_nat(x_72);
x_74 = lean_usize_sub(x_71, x_73);
x_75 = lean_usize_land(x_70, x_74);
x_76 = lean_array_uget(x_56, x_75);
lean_dec(x_56);
x_77 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_59, x_13, x_76);
lean_dec(x_76);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_array_get_size(x_78);
x_80 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_81 = lean_uint64_shift_right(x_80, x_63);
x_82 = lean_uint64_xor(x_80, x_81);
x_83 = lean_uint64_shift_right(x_82, x_67);
x_84 = lean_uint64_xor(x_82, x_83);
x_85 = lean_uint64_to_usize(x_84);
x_86 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_87 = lean_usize_sub(x_86, x_73);
x_88 = lean_usize_land(x_85, x_87);
x_89 = lean_array_uget(x_78, x_88);
lean_dec(x_78);
x_90 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_89);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_55);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_55);
return x_94;
}
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_8);
x_95 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_4);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; lean_object* x_118; size_t x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; size_t x_131; size_t x_132; size_t x_133; size_t x_134; lean_object* x_135; lean_object* x_136; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_st_ref_get(x_3, x_4);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = l_Lean_instBEqFVarId;
x_104 = l_Lean_instHashableFVarId;
x_105 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_103, x_104);
x_106 = lean_array_get_size(x_102);
x_107 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_97);
x_108 = lean_unsigned_to_nat(32u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_unsigned_to_nat(16u);
x_113 = lean_uint64_of_nat(x_112);
x_114 = lean_uint64_shift_right(x_111, x_113);
x_115 = lean_uint64_xor(x_111, x_114);
x_116 = lean_uint64_to_usize(x_115);
x_117 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_usize_of_nat(x_118);
x_120 = lean_usize_sub(x_117, x_119);
x_121 = lean_usize_land(x_116, x_120);
x_122 = lean_array_uget(x_102, x_121);
lean_dec(x_102);
x_123 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_105, x_97, x_122);
lean_dec(x_122);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_array_get_size(x_124);
x_126 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_127 = lean_uint64_shift_right(x_126, x_109);
x_128 = lean_uint64_xor(x_126, x_127);
x_129 = lean_uint64_shift_right(x_128, x_113);
x_130 = lean_uint64_xor(x_128, x_129);
x_131 = lean_uint64_to_usize(x_130);
x_132 = lean_usize_of_nat(x_125);
lean_dec(x_125);
x_133 = lean_usize_sub(x_132, x_119);
x_134 = lean_usize_land(x_131, x_133);
x_135 = lean_array_uget(x_124, x_134);
lean_dec(x_124);
x_136 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_135);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
if (lean_is_scalar(x_101)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_101;
}
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_100);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_1);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
if (lean_is_scalar(x_101)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_101;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_100);
return x_140;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg(x_1, x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(x_1, x_5, x_10);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = l_Lean_FVarIdSet_insert(x_18, x_1);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_12);
x_20 = lean_apply_8(x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = l_Lean_FVarIdSet_insert(x_22, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_apply_8(x_2, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_FVarIdSet_insert(x_4, x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_6 = x_10;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_17; 
x_17 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
x_12 = x_18;
x_13 = x_10;
goto block_16;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
x_12 = x_18;
x_13 = x_10;
goto block_16;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_usize_of_nat(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___redArg(x_1, x_23, x_24, x_18, x_5, x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_12 = x_26;
x_13 = x_27;
goto block_16;
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_apply_8(x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_48; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_st_ref_get(x_3, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_26);
x_28 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_22);
x_29 = lean_unsigned_to_nat(32u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_unsigned_to_nat(16u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_usize_of_nat(x_38);
x_40 = lean_usize_sub(x_37, x_39);
x_41 = l_Lean_Compiler_LCNF_ScopeM_isInScope___redArg(x_1, x_4, x_25);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_48 = lean_unbox(x_42);
lean_dec(x_42);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; size_t x_63; size_t x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_49 = l_Lean_instBEqFVarId;
x_50 = l_Lean_instHashableFVarId;
x_51 = lean_uint64_to_usize(x_36);
x_52 = lean_usize_land(x_51, x_40);
x_53 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_49, x_50);
x_54 = lean_array_uget(x_26, x_52);
lean_dec(x_26);
x_55 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_53, x_22, x_54);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = lean_array_get_size(x_56);
x_58 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_59 = lean_uint64_shift_right(x_58, x_30);
x_60 = lean_uint64_xor(x_58, x_59);
x_61 = lean_uint64_shift_right(x_60, x_34);
x_62 = lean_uint64_xor(x_60, x_61);
x_63 = lean_uint64_to_usize(x_62);
x_64 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_65 = lean_usize_sub(x_64, x_39);
x_66 = lean_usize_land(x_63, x_65);
x_67 = lean_array_uget(x_56, x_66);
lean_dec(x_56);
x_68 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
lean_dec(x_2);
x_70 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_69, x_1);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_dec(x_55);
lean_dec(x_22);
lean_dec(x_1);
goto block_47;
}
else
{
lean_object* x_71; 
lean_dec(x_70);
lean_dec(x_44);
lean_inc(x_1);
x_71 = l_Lean_Compiler_LCNF_getType(x_1, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_132; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Compiler_LCNF_mkAuxParam(x_72, x_68, x_5, x_6, x_7, x_8, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_132 = !lean_is_exclusive(x_55);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; uint8_t x_140; 
x_133 = lean_ctor_get(x_55, 0);
x_134 = lean_ctor_get(x_55, 1);
x_135 = lean_array_get_size(x_134);
x_136 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_137 = lean_usize_sub(x_136, x_39);
x_138 = lean_usize_land(x_63, x_137);
x_139 = lean_array_uget(x_134, x_138);
x_140 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_141 = lean_nat_add(x_133, x_38);
lean_dec(x_133);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_75);
lean_ctor_set(x_142, 2, x_139);
x_143 = lean_array_uset(x_134, x_138, x_142);
x_144 = lean_unsigned_to_nat(2u);
x_145 = lean_nat_shiftl(x_141, x_144);
x_146 = lean_unsigned_to_nat(3u);
x_147 = lean_nat_div(x_145, x_146);
lean_dec(x_145);
x_148 = lean_array_get_size(x_143);
x_149 = lean_nat_dec_le(x_147, x_148);
lean_dec(x_148);
lean_dec(x_147);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_143);
lean_ctor_set(x_55, 1, x_150);
lean_ctor_set(x_55, 0, x_141);
x_77 = x_55;
goto block_131;
}
else
{
lean_ctor_set(x_55, 1, x_143);
lean_ctor_set(x_55, 0, x_141);
x_77 = x_55;
goto block_131;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_box(0);
x_152 = lean_array_uset(x_134, x_138, x_151);
x_153 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_75, x_139);
x_154 = lean_array_uset(x_152, x_138, x_153);
lean_ctor_set(x_55, 1, x_154);
x_77 = x_55;
goto block_131;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; size_t x_158; size_t x_159; size_t x_160; lean_object* x_161; uint8_t x_162; 
x_155 = lean_ctor_get(x_55, 0);
x_156 = lean_ctor_get(x_55, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_55);
x_157 = lean_array_get_size(x_156);
x_158 = lean_usize_of_nat(x_157);
lean_dec(x_157);
x_159 = lean_usize_sub(x_158, x_39);
x_160 = lean_usize_land(x_63, x_159);
x_161 = lean_array_uget(x_156, x_160);
x_162 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_163 = lean_nat_add(x_155, x_38);
lean_dec(x_155);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_75);
lean_ctor_set(x_164, 2, x_161);
x_165 = lean_array_uset(x_156, x_160, x_164);
x_166 = lean_unsigned_to_nat(2u);
x_167 = lean_nat_shiftl(x_163, x_166);
x_168 = lean_unsigned_to_nat(3u);
x_169 = lean_nat_div(x_167, x_168);
lean_dec(x_167);
x_170 = lean_array_get_size(x_165);
x_171 = lean_nat_dec_le(x_169, x_170);
lean_dec(x_170);
lean_dec(x_169);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_165);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_163);
lean_ctor_set(x_173, 1, x_172);
x_77 = x_173;
goto block_131;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_163);
lean_ctor_set(x_174, 1, x_165);
x_77 = x_174;
goto block_131;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_box(0);
x_176 = lean_array_uset(x_156, x_160, x_175);
x_177 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_75, x_161);
x_178 = lean_array_uset(x_176, x_160, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_155);
lean_ctor_set(x_179, 1, x_178);
x_77 = x_179;
goto block_131;
}
}
block_131:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_st_ref_take(x_3, x_76);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; size_t x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 1);
x_84 = lean_box(0);
x_85 = lean_array_get_size(x_83);
x_86 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_87 = lean_usize_sub(x_86, x_39);
x_88 = lean_usize_land(x_51, x_87);
x_89 = lean_array_uget(x_83, x_88);
x_90 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_22, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_91 = lean_nat_add(x_82, x_38);
lean_dec(x_82);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_22);
lean_ctor_set(x_92, 1, x_77);
lean_ctor_set(x_92, 2, x_89);
x_93 = lean_array_uset(x_83, x_88, x_92);
x_94 = lean_unsigned_to_nat(2u);
x_95 = lean_nat_shiftl(x_91, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = lean_nat_div(x_95, x_96);
lean_dec(x_95);
x_98 = lean_array_get_size(x_93);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_93);
lean_ctor_set(x_79, 1, x_100);
lean_ctor_set(x_79, 0, x_91);
x_10 = x_80;
x_11 = x_84;
x_12 = x_79;
goto block_18;
}
else
{
lean_ctor_set(x_79, 1, x_93);
lean_ctor_set(x_79, 0, x_91);
x_10 = x_80;
x_11 = x_84;
x_12 = x_79;
goto block_18;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_box(0);
x_102 = lean_array_uset(x_83, x_88, x_101);
x_103 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_22, x_77, x_89);
x_104 = lean_array_uset(x_102, x_88, x_103);
lean_ctor_set(x_79, 1, x_104);
x_10 = x_80;
x_11 = x_84;
x_12 = x_79;
goto block_18;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; size_t x_110; size_t x_111; lean_object* x_112; uint8_t x_113; 
x_105 = lean_ctor_get(x_79, 0);
x_106 = lean_ctor_get(x_79, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_79);
x_107 = lean_box(0);
x_108 = lean_array_get_size(x_106);
x_109 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_110 = lean_usize_sub(x_109, x_39);
x_111 = lean_usize_land(x_51, x_110);
x_112 = lean_array_uget(x_106, x_111);
x_113 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_22, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_114 = lean_nat_add(x_105, x_38);
lean_dec(x_105);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_22);
lean_ctor_set(x_115, 1, x_77);
lean_ctor_set(x_115, 2, x_112);
x_116 = lean_array_uset(x_106, x_111, x_115);
x_117 = lean_unsigned_to_nat(2u);
x_118 = lean_nat_shiftl(x_114, x_117);
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_nat_div(x_118, x_119);
lean_dec(x_118);
x_121 = lean_array_get_size(x_116);
x_122 = lean_nat_dec_le(x_120, x_121);
lean_dec(x_121);
lean_dec(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_116);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_114);
lean_ctor_set(x_124, 1, x_123);
x_10 = x_80;
x_11 = x_107;
x_12 = x_124;
goto block_18;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_114);
lean_ctor_set(x_125, 1, x_116);
x_10 = x_80;
x_11 = x_107;
x_12 = x_125;
goto block_18;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_box(0);
x_127 = lean_array_uset(x_106, x_111, x_126);
x_128 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_22, x_77, x_112);
x_129 = lean_array_uset(x_127, x_111, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_105);
lean_ctor_set(x_130, 1, x_129);
x_10 = x_80;
x_11 = x_107;
x_12 = x_130;
goto block_18;
}
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_55);
lean_dec(x_22);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_71);
if (x_180 == 0)
{
return x_71;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_71, 0);
x_182 = lean_ctor_get(x_71, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_71);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
else
{
lean_dec(x_55);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
goto block_47;
}
}
else
{
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
goto block_47;
}
block_47:
{
lean_object* x_45; lean_object* x_46; 
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
block_18:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_set(x_3, x_12, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_5);
x_17 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_4 = x_19;
x_12 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; lean_object* x_43; size_t x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_10);
x_13 = lean_st_ref_get(x_3, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = l_Lean_instBEqFVarId;
x_29 = l_Lean_instHashableFVarId;
x_30 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_28, x_29);
x_31 = lean_array_get_size(x_27);
x_32 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_33 = lean_unsigned_to_nat(32u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_unsigned_to_nat(16u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_right(x_36, x_38);
x_40 = lean_uint64_xor(x_36, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_usize_of_nat(x_43);
x_45 = lean_usize_sub(x_42, x_44);
x_46 = lean_usize_land(x_41, x_45);
x_47 = lean_array_uget(x_27, x_46);
lean_dec(x_27);
x_48 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_30, x_1, x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_mk_empty_array_with_capacity(x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_array_get_size(x_51);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_51);
x_16 = x_50;
goto block_26;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_53, x_53);
if (x_55 == 0)
{
lean_dec(x_53);
lean_dec(x_51);
x_16 = x_50;
goto block_26;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = lean_usize_of_nat(x_52);
x_57 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_58 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LCtx_toLocalContext_spec__8(x_51, x_56, x_57, x_50);
lean_dec(x_51);
x_16 = x_58;
goto block_26;
}
}
block_26:
{
lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_box(0);
x_18 = lean_array_size(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary_spec__0(x_16, x_18, x_20, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(x_4, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg___lam__0), 9, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0_spec__0___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___redArg(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_take(x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_shiftl(x_18, x_19);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_div(x_20, x_21);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; size_t x_51; size_t x_52; lean_object* x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; uint8_t x_58; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_ctor_set(x_11, 1, x_17);
lean_ctor_set(x_11, 0, x_16);
x_37 = l_Nat_nextPowerOfTwo(x_22);
lean_dec(x_22);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_mk_array(x_37, x_38);
lean_ctor_set(x_13, 1, x_40);
lean_ctor_set(x_13, 0, x_39);
x_41 = lean_array_get_size(x_25);
x_42 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_15);
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
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_usize_of_nat(x_53);
x_55 = lean_usize_sub(x_52, x_54);
x_56 = lean_usize_land(x_51, x_55);
x_57 = lean_array_uget(x_25, x_56);
x_58 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_15, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_nat_add(x_24, x_53);
lean_dec(x_24);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_13);
lean_ctor_set(x_60, 2, x_57);
x_61 = lean_array_uset(x_25, x_56, x_60);
x_62 = lean_nat_shiftl(x_59, x_19);
x_63 = lean_nat_div(x_62, x_21);
lean_dec(x_62);
x_64 = lean_array_get_size(x_61);
x_65 = lean_nat_dec_le(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_66);
x_26 = x_67;
goto block_36;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_61);
x_26 = x_68;
goto block_36;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_array_uset(x_25, x_56, x_38);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_15, x_13, x_57);
x_71 = lean_array_uset(x_69, x_56, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_24);
lean_ctor_set(x_72, 1, x_71);
x_26 = x_72;
goto block_36;
}
block_36:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_st_ref_set(x_4, x_26, x_14);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_array_size(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_usize_of_nat(x_31);
x_33 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0(x_30, x_32, x_29);
x_34 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___boxed), 11, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_2);
x_35 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg(x_34, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
return x_35;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; lean_object* x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; size_t x_101; size_t x_102; lean_object* x_103; size_t x_104; size_t x_105; size_t x_106; lean_object* x_107; uint8_t x_108; 
x_73 = lean_ctor_get(x_13, 0);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_13);
lean_inc(x_17);
lean_ctor_set(x_11, 1, x_17);
lean_ctor_set(x_11, 0, x_16);
x_86 = l_Nat_nextPowerOfTwo(x_22);
lean_dec(x_22);
x_87 = lean_box(0);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_mk_array(x_86, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_array_get_size(x_74);
x_92 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_15);
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
x_107 = lean_array_uget(x_74, x_106);
x_108 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_15, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_nat_add(x_73, x_103);
lean_dec(x_73);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_15);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_110, 2, x_107);
x_111 = lean_array_uset(x_74, x_106, x_110);
x_112 = lean_nat_shiftl(x_109, x_19);
x_113 = lean_nat_div(x_112, x_21);
lean_dec(x_112);
x_114 = lean_array_get_size(x_111);
x_115 = lean_nat_dec_le(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_111);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_109);
lean_ctor_set(x_117, 1, x_116);
x_75 = x_117;
goto block_85;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_109);
lean_ctor_set(x_118, 1, x_111);
x_75 = x_118;
goto block_85;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_array_uset(x_74, x_106, x_87);
x_120 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_15, x_90, x_107);
x_121 = lean_array_uset(x_119, x_106, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_73);
lean_ctor_set(x_122, 1, x_121);
x_75 = x_122;
goto block_85;
}
block_85:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; lean_object* x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_st_ref_set(x_4, x_75, x_14);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
lean_dec(x_1);
x_79 = lean_array_size(x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_usize_of_nat(x_80);
x_82 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0(x_79, x_81, x_78);
x_83 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___boxed), 11, 3);
lean_closure_set(x_83, 0, lean_box(0));
lean_closure_set(x_83, 1, x_82);
lean_closure_set(x_83, 2, x_2);
x_84 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg(x_83, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
return x_84;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint64_t x_154; lean_object* x_155; uint64_t x_156; uint64_t x_157; uint64_t x_158; lean_object* x_159; uint64_t x_160; uint64_t x_161; uint64_t x_162; size_t x_163; size_t x_164; lean_object* x_165; size_t x_166; size_t x_167; size_t x_168; lean_object* x_169; uint8_t x_170; 
x_123 = lean_ctor_get(x_11, 0);
x_124 = lean_ctor_get(x_11, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_11);
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
lean_inc(x_125);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_ctor_get(x_3, 1);
x_128 = lean_unsigned_to_nat(8u);
x_129 = lean_unsigned_to_nat(2u);
x_130 = lean_nat_shiftl(x_128, x_129);
x_131 = lean_unsigned_to_nat(3u);
x_132 = lean_nat_div(x_130, x_131);
lean_dec(x_130);
x_133 = lean_ctor_get(x_123, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_123, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_135 = x_123;
} else {
 lean_dec_ref(x_123);
 x_135 = lean_box(0);
}
lean_inc(x_127);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_126);
lean_ctor_set(x_136, 1, x_127);
x_148 = l_Nat_nextPowerOfTwo(x_132);
lean_dec(x_132);
x_149 = lean_box(0);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_mk_array(x_148, x_149);
if (lean_is_scalar(x_135)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_135;
}
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_array_get_size(x_134);
x_154 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_125);
x_155 = lean_unsigned_to_nat(32u);
x_156 = lean_uint64_of_nat(x_155);
x_157 = lean_uint64_shift_right(x_154, x_156);
x_158 = lean_uint64_xor(x_154, x_157);
x_159 = lean_unsigned_to_nat(16u);
x_160 = lean_uint64_of_nat(x_159);
x_161 = lean_uint64_shift_right(x_158, x_160);
x_162 = lean_uint64_xor(x_158, x_161);
x_163 = lean_uint64_to_usize(x_162);
x_164 = lean_usize_of_nat(x_153);
lean_dec(x_153);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_usize_of_nat(x_165);
x_167 = lean_usize_sub(x_164, x_166);
x_168 = lean_usize_land(x_163, x_167);
x_169 = lean_array_uget(x_134, x_168);
x_170 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_125, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_171 = lean_nat_add(x_133, x_165);
lean_dec(x_133);
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_125);
lean_ctor_set(x_172, 1, x_152);
lean_ctor_set(x_172, 2, x_169);
x_173 = lean_array_uset(x_134, x_168, x_172);
x_174 = lean_nat_shiftl(x_171, x_129);
x_175 = lean_nat_div(x_174, x_131);
lean_dec(x_174);
x_176 = lean_array_get_size(x_173);
x_177 = lean_nat_dec_le(x_175, x_176);
lean_dec(x_176);
lean_dec(x_175);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_173);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_171);
lean_ctor_set(x_179, 1, x_178);
x_137 = x_179;
goto block_147;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_171);
lean_ctor_set(x_180, 1, x_173);
x_137 = x_180;
goto block_147;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_array_uset(x_134, x_168, x_149);
x_182 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_125, x_152, x_169);
x_183 = lean_array_uset(x_181, x_168, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_133);
lean_ctor_set(x_184, 1, x_183);
x_137 = x_184;
goto block_147;
}
block_147:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; size_t x_141; lean_object* x_142; size_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_138 = lean_st_ref_set(x_4, x_137, x_124);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_ctor_get(x_1, 2);
lean_inc(x_140);
lean_dec(x_1);
x_141 = lean_array_size(x_140);
x_142 = lean_unsigned_to_nat(0u);
x_143 = lean_usize_of_nat(x_142);
x_144 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0(x_141, x_143, x_140);
x_145 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___boxed), 11, 3);
lean_closure_set(x_145, 0, lean_box(0));
lean_closure_set(x_145, 1, x_144);
lean_closure_set(x_145, 2, x_2);
x_146 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0___redArg(x_145, x_136, x_4, x_5, x_6, x_7, x_8, x_9, x_139);
return x_146;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Compiler_LCNF_AltCore_getParams(x_1);
x_12 = lean_array_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
x_15 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope_spec__0(x_12, x_14, x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___boxed), 11, 3);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_2);
x_17 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope_spec__0_spec__0___redArg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg(x_1, x_2, x_3, x_11);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_11 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_11 = x_26;
goto block_24;
}
block_24:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_14 = l_instMonadEIO(lean_box(0));
x_15 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
lean_inc(x_29);
lean_inc(x_26);
lean_inc(x_23);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_23);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_26);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_29);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_10);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
x_46 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_45);
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
x_48 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_47);
x_49 = l_Lean_instInhabitedExpr;
x_50 = l_instInhabitedOfMonad___redArg(x_48, x_49);
x_51 = lean_panic_fn(x_50, x_1);
x_52 = lean_apply_8(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_52;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_inc(x_11);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = l_Lean_Expr_fvar___override(x_14);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_11, x_17);
lean_dec(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = l_Lean_Expr_fvar___override(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_28 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.mapFVarM", 32, 32);
x_29 = lean_unsigned_to_nat(27u);
x_30 = lean_unsigned_to_nat(39u);
x_31 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_32 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_27, x_28, x_29, x_30, x_31);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
x_33 = l_panic___at___Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1_spec__1(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_33;
}
case 5:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_34);
lean_inc(x_1);
x_36 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_35);
x_39 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(x_1, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; size_t x_48; size_t x_49; uint8_t x_50; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_48 = lean_ptr_addr(x_34);
lean_dec(x_34);
x_49 = lean_ptr_addr(x_37);
x_50 = lean_usize_dec_eq(x_48, x_49);
if (x_50 == 0)
{
lean_dec(x_35);
x_43 = x_50;
goto block_47;
}
else
{
size_t x_51; size_t x_52; uint8_t x_53; 
x_51 = lean_ptr_addr(x_35);
lean_dec(x_35);
x_52 = lean_ptr_addr(x_40);
x_53 = lean_usize_dec_eq(x_51, x_52);
x_43 = x_53;
goto block_47;
}
block_47:
{
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_44 = l_Lean_Expr_app___override(x_37, x_40);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_37);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
case 6:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_55);
lean_inc(x_1);
x_58 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(x_1, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_56);
x_61 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(x_1, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Expr_lam___override(x_54, x_55, x_56, x_57);
if (lean_obj_tag(x_65) == 6)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; size_t x_78; size_t x_79; uint8_t x_80; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_65, sizeof(void*)*3 + 8);
x_78 = lean_ptr_addr(x_67);
lean_dec(x_67);
x_79 = lean_ptr_addr(x_59);
x_80 = lean_usize_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_dec(x_68);
x_70 = x_80;
goto block_77;
}
else
{
size_t x_81; size_t x_82; uint8_t x_83; 
x_81 = lean_ptr_addr(x_68);
lean_dec(x_68);
x_82 = lean_ptr_addr(x_62);
x_83 = lean_usize_dec_eq(x_81, x_82);
x_70 = x_83;
goto block_77;
}
block_77:
{
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
x_71 = l_Lean_Expr_lam___override(x_66, x_59, x_62, x_57);
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_63);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_69, x_57);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_65);
x_74 = l_Lean_Expr_lam___override(x_66, x_59, x_62, x_57);
if (lean_is_scalar(x_64)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_64;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_63);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_59);
if (lean_is_scalar(x_64)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_64;
}
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_63);
return x_76;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_59);
x_84 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_85 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_86 = lean_unsigned_to_nat(1848u);
x_87 = lean_unsigned_to_nat(19u);
x_88 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_89 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_84, x_85, x_86, x_87, x_88);
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_84);
x_90 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_89);
if (lean_is_scalar(x_64)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_64;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_63);
return x_91;
}
}
else
{
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
return x_61;
}
}
else
{
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_58;
}
}
case 7:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_2, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 2);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_93);
lean_inc(x_1);
x_96 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(x_1, x_93, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_94);
x_99 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(x_1, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = l_Lean_Expr_forallE___override(x_92, x_93, x_94, x_95);
if (lean_obj_tag(x_103) == 7)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; size_t x_116; size_t x_117; uint8_t x_118; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_103, sizeof(void*)*3 + 8);
x_116 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_117 = lean_ptr_addr(x_97);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_dec(x_106);
x_108 = x_118;
goto block_115;
}
else
{
size_t x_119; size_t x_120; uint8_t x_121; 
x_119 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_120 = lean_ptr_addr(x_100);
x_121 = lean_usize_dec_eq(x_119, x_120);
x_108 = x_121;
goto block_115;
}
block_115:
{
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_103);
x_109 = l_Lean_Expr_forallE___override(x_104, x_97, x_100, x_95);
if (lean_is_scalar(x_102)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_102;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_101);
return x_110;
}
else
{
uint8_t x_111; 
x_111 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_107, x_95);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_103);
x_112 = l_Lean_Expr_forallE___override(x_104, x_97, x_100, x_95);
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_102;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_101);
return x_113;
}
else
{
lean_object* x_114; 
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_97);
if (lean_is_scalar(x_102)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_102;
}
lean_ctor_set(x_114, 0, x_103);
lean_ctor_set(x_114, 1, x_101);
return x_114;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_97);
x_122 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_123 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_124 = lean_unsigned_to_nat(1828u);
x_125 = lean_unsigned_to_nat(23u);
x_126 = lean_mk_string_unchecked("forall expected", 15, 15);
x_127 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_122, x_123, x_124, x_125, x_126);
lean_dec(x_126);
lean_dec(x_123);
lean_dec(x_122);
x_128 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_127);
if (lean_is_scalar(x_102)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_102;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_101);
return x_129;
}
}
else
{
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
return x_99;
}
}
else
{
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_96;
}
}
case 8:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_131 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.mapFVarM", 32, 32);
x_132 = lean_unsigned_to_nat(27u);
x_133 = lean_unsigned_to_nat(39u);
x_134 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_135 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_130, x_131, x_132, x_133, x_134);
lean_dec(x_134);
lean_dec(x_131);
lean_dec(x_130);
x_136 = l_panic___at___Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1_spec__1(x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_136;
}
case 11:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_138 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.mapFVarM", 32, 32);
x_139 = lean_unsigned_to_nat(27u);
x_140 = lean_unsigned_to_nat(39u);
x_141 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_142 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_137, x_138, x_139, x_140, x_141);
lean_dec(x_141);
lean_dec(x_138);
lean_dec(x_137);
x_143 = l_panic___at___Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1_spec__1(x_142, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_143;
}
default: 
{
lean_object* x_144; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_2);
lean_ctor_set(x_144, 1, x_10);
return x_144;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_apply_9(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(x_2, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(x_2, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at___Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1_spec__1(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_2, x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_2, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_4, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1(x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_4, x_3, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_20, x_3, x_17);
x_3 = x_23;
x_4 = x_24;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_2, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
case 3:
{
lean_object* x_24; size_t x_25; lean_object* x_26; size_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_array_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_usize_of_nat(x_26);
x_28 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__4(x_1, x_25, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_2, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_2, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
case 4:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = lean_apply_9(x_1, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_size(x_41);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_usize_of_nat(x_46);
x_48 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__4(x_1, x_45, x_47, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_2, x_43, x_50);
lean_dec(x_2);
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
x_54 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_2, x_43, x_52);
lean_dec(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_43);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 0);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
default: 
{
lean_object* x_64; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_10);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Expr_forallE___override(x_10, x_11, x_4, x_13);
x_2 = x_8;
x_4 = x_14;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__8(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar___boxed), 9, 0);
x_15 = lean_array_uget(x_3, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_Arg_mapFVarM___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__1(x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_3, x_2, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_20, x_2, x_17);
x_2 = x_23;
x_3 = x_24;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__9(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__10(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__11(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_3, x_2);
lean_inc(x_4);
x_15 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_array_uset(x_3, x_2, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_19, x_2, x_20);
x_2 = x_23;
x_3 = x_24;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__12(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 0);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__0), 10, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___redArg(x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_3, x_2, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_2, x_23);
x_25 = lean_array_uset(x_21, x_2, x_18);
x_2 = x_24;
x_3 = x_25;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; size_t x_22; size_t x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_22 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_23 = lean_ptr_addr(x_14);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
x_17 = x_24;
goto block_21;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_4);
x_26 = lean_ptr_addr(x_2);
x_27 = lean_usize_dec_eq(x_25, x_26);
x_17 = x_27;
goto block_21;
}
block_21:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_14);
if (lean_is_scalar(x_16)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_16;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_2);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_7);
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_2, x_14, x_15, x_12, x_7, x_13);
lean_dec(x_7);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; size_t x_22; size_t x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_22 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_23 = lean_ptr_addr(x_14);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
x_17 = x_24;
goto block_21;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_4);
x_26 = lean_ptr_addr(x_2);
x_27 = lean_usize_dec_eq(x_25, x_26);
x_17 = x_27;
goto block_21;
}
block_21:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_14);
if (lean_is_scalar(x_16)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_16;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_2);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_8);
lean_inc(x_5);
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; lean_object* x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_5, x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_35);
x_38 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_36);
x_39 = lean_unsigned_to_nat(32u);
x_40 = lean_uint64_of_nat(x_39);
x_41 = lean_uint64_shift_right(x_38, x_40);
x_42 = lean_uint64_xor(x_38, x_41);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_uint64_of_nat(x_43);
x_45 = lean_uint64_shift_right(x_42, x_44);
x_46 = lean_uint64_xor(x_42, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_usize_of_nat(x_49);
x_51 = lean_usize_sub(x_48, x_50);
x_52 = lean_usize_land(x_47, x_51);
x_53 = lean_array_uget(x_35, x_52);
lean_dec(x_35);
x_54 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_3, x_36, x_53);
lean_dec(x_53);
lean_dec(x_36);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_mk_empty_array_with_capacity(x_55);
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_57);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec(x_57);
x_24 = x_56;
goto block_34;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_59, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec(x_57);
x_24 = x_56;
goto block_34;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
x_62 = lean_usize_of_nat(x_58);
x_63 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_64 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LCtx_toLocalContext_spec__8(x_57, x_62, x_63, x_56);
lean_dec(x_57);
x_24 = x_64;
goto block_34;
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = l_Array_append(lean_box(0), x_18, x_20);
lean_dec(x_20);
x_22 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_2, x_19, x_21, x_13, x_8, x_17);
lean_dec(x_8);
return x_22;
}
block_34:
{
size_t x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_array_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_usize_of_nat(x_26);
x_28 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__6(x_25, x_27, x_24);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
x_30 = lean_array_get_size(x_28);
x_31 = lean_nat_dec_lt(x_26, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
x_18 = x_28;
x_19 = x_29;
goto block_23;
}
else
{
size_t x_32; lean_object* x_33; 
x_32 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_33 = l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__7(x_28, x_32, x_27, x_29);
x_18 = x_28;
x_19 = x_33;
goto block_23;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_12);
if (x_65 == 0)
{
return x_12;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_12, 0);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_12);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; size_t x_22; size_t x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_22 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_23 = lean_ptr_addr(x_14);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
x_17 = x_24;
goto block_21;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_4);
x_26 = lean_ptr_addr(x_2);
x_27 = lean_usize_dec_eq(x_25, x_26);
x_17 = x_27;
goto block_21;
}
block_21:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_14);
if (lean_is_scalar(x_16)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_16;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_2);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_instBEqFVarId;
x_11 = l_Lean_instHashableFVarId;
x_12 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_10, x_11);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar___boxed), 9, 0);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_13);
x_20 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_13, x_18, x_5, x_6, x_7, x_8, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__0___boxed), 12, 4);
lean_closure_set(x_23, 0, x_14);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_1);
lean_closure_set(x_23, 3, x_13);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___redArg(x_24, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 4);
lean_inc(x_32);
lean_inc(x_30);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__1), 10, 2);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___redArg(x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_35);
x_37 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__2___boxed), 12, 4);
lean_closure_set(x_37, 0, x_31);
lean_closure_set(x_37, 1, x_35);
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, x_30);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___redArg(x_38, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 2:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 4);
lean_inc(x_46);
lean_inc(x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__3), 11, 3);
lean_closure_set(x_47, 0, x_46);
lean_closure_set(x_47, 1, x_44);
lean_closure_set(x_47, 2, x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_44);
x_48 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___redArg(x_44, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_inc(x_2);
x_52 = l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__4___boxed), 12, 4);
lean_closure_set(x_54, 0, x_45);
lean_closure_set(x_54, 1, x_49);
lean_closure_set(x_54, 2, x_1);
lean_closure_set(x_54, 3, x_44);
x_55 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___redArg(x_51, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
return x_48;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
case 3:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_77; lean_object* x_78; size_t x_84; lean_object* x_85; size_t x_86; lean_object* x_87; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_84 = lean_array_size(x_65);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_usize_of_nat(x_85);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_65);
x_87 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__8(x_84, x_86, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_110; lean_object* x_111; uint64_t x_112; lean_object* x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; lean_object* x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; size_t x_121; size_t x_122; lean_object* x_123; size_t x_124; size_t x_125; size_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_3, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_110 = lean_ctor_get(x_91, 1);
lean_inc(x_110);
lean_dec(x_91);
x_111 = lean_array_get_size(x_110);
x_112 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_64);
x_113 = lean_unsigned_to_nat(32u);
x_114 = lean_uint64_of_nat(x_113);
x_115 = lean_uint64_shift_right(x_112, x_114);
x_116 = lean_uint64_xor(x_112, x_115);
x_117 = lean_unsigned_to_nat(16u);
x_118 = lean_uint64_of_nat(x_117);
x_119 = lean_uint64_shift_right(x_116, x_118);
x_120 = lean_uint64_xor(x_116, x_119);
x_121 = lean_uint64_to_usize(x_120);
x_122 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_usize_of_nat(x_123);
x_125 = lean_usize_sub(x_122, x_124);
x_126 = lean_usize_land(x_121, x_125);
x_127 = lean_array_uget(x_110, x_126);
lean_dec(x_110);
x_128 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar_spec__0___redArg(x_12, x_64, x_127);
lean_dec(x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_mk_empty_array_with_capacity(x_129);
lean_dec(x_129);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_85, x_132);
if (x_133 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
x_93 = x_130;
goto block_109;
}
else
{
uint8_t x_134; 
x_134 = lean_nat_dec_le(x_132, x_132);
if (x_134 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
x_93 = x_130;
goto block_109;
}
else
{
size_t x_135; lean_object* x_136; 
x_135 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_136 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LCtx_toLocalContext_spec__8(x_131, x_86, x_135, x_130);
lean_dec(x_131);
x_93 = x_136;
goto block_109;
}
}
block_109:
{
size_t x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_array_size(x_93);
x_95 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__9(x_94, x_86, x_93);
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
size_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = lean_array_size(x_95);
x_98 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__10(x_97, x_86, x_95);
x_99 = l_Array_append(lean_box(0), x_98, x_88);
lean_dec(x_88);
x_77 = x_99;
x_78 = x_92;
goto block_83;
}
else
{
size_t x_100; lean_object* x_101; 
lean_dec(x_96);
x_100 = lean_array_size(x_95);
x_101 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__11(x_100, x_86, x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_92);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Array_append(lean_box(0), x_102, x_88);
lean_dec(x_88);
x_77 = x_104;
x_78 = x_103;
goto block_83;
}
else
{
uint8_t x_105; 
lean_dec(x_88);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_101);
if (x_105 == 0)
{
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_87);
if (x_137 == 0)
{
return x_87;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_87, 0);
x_139 = lean_ctor_get(x_87, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_87);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
block_76:
{
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_1);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_1, 1);
lean_dec(x_70);
x_71 = lean_ctor_get(x_1, 0);
lean_dec(x_71);
lean_ctor_set(x_1, 1, x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_73 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_67);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_67);
lean_dec(x_64);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_66);
return x_75;
}
}
block_83:
{
uint8_t x_79; 
x_79 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_64, x_64);
if (x_79 == 0)
{
lean_dec(x_65);
x_66 = x_78;
x_67 = x_77;
x_68 = x_79;
goto block_76;
}
else
{
size_t x_80; size_t x_81; uint8_t x_82; 
x_80 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_81 = lean_ptr_addr(x_77);
x_82 = lean_usize_dec_eq(x_80, x_81);
x_66 = x_78;
x_67 = x_77;
x_68 = x_82;
goto block_76;
}
}
}
case 4:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_12);
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 2);
lean_inc(x_142);
lean_inc(x_2);
lean_inc(x_142);
x_143 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_142, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; size_t x_150; lean_object* x_151; size_t x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
lean_inc(x_142);
x_145 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg(x_142, x_2, x_3, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_141, 3);
lean_inc(x_149);
x_150 = lean_array_size(x_149);
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_usize_of_nat(x_151);
lean_inc(x_149);
x_153 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__12(x_150, x_152, x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_147);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_163; size_t x_167; size_t x_168; uint8_t x_169; 
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
x_157 = lean_ctor_get(x_141, 1);
lean_inc(x_157);
x_167 = lean_ptr_addr(x_149);
lean_dec(x_149);
x_168 = lean_ptr_addr(x_154);
x_169 = lean_usize_dec_eq(x_167, x_168);
if (x_169 == 0)
{
x_163 = x_169;
goto block_166;
}
else
{
size_t x_170; uint8_t x_171; 
x_170 = lean_ptr_addr(x_157);
x_171 = lean_usize_dec_eq(x_170, x_170);
x_163 = x_171;
goto block_166;
}
block_162:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_141, 0);
lean_inc(x_158);
lean_dec(x_141);
x_159 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
lean_ctor_set(x_159, 2, x_146);
lean_ctor_set(x_159, 3, x_154);
x_160 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_160, 0, x_159);
if (lean_is_scalar(x_156)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_156;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_155);
return x_161;
}
block_166:
{
if (x_163 == 0)
{
lean_dec(x_148);
lean_dec(x_142);
lean_dec(x_1);
goto block_162;
}
else
{
uint8_t x_164; 
x_164 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_142, x_146);
lean_dec(x_142);
if (x_164 == 0)
{
lean_dec(x_148);
lean_dec(x_1);
goto block_162;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_146);
lean_dec(x_141);
if (lean_is_scalar(x_148)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_148;
}
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_155);
return x_165;
}
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_153);
if (x_172 == 0)
{
return x_153;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_153, 0);
x_174 = lean_ctor_get(x_153, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_153);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_143);
if (x_176 == 0)
{
return x_143;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_143, 0);
x_178 = lean_ctor_get(x_143, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_143);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
case 5:
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_12);
x_180 = lean_ctor_get(x_1, 0);
lean_inc(x_180);
lean_inc(x_2);
lean_inc(x_180);
x_181 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_180, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
lean_inc(x_180);
x_183 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___redArg(x_180, x_2, x_3, x_182);
lean_dec(x_3);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_180, x_185);
lean_dec(x_180);
if (x_186 == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_1);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_1, 0);
lean_dec(x_188);
lean_ctor_set(x_1, 0, x_185);
lean_ctor_set(x_183, 0, x_1);
return x_183;
}
else
{
lean_object* x_189; 
lean_dec(x_1);
x_189 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_183, 0, x_189);
return x_183;
}
}
else
{
lean_dec(x_185);
lean_ctor_set(x_183, 0, x_1);
return x_183;
}
}
else
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_190 = lean_ctor_get(x_183, 0);
x_191 = lean_ctor_get(x_183, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_183);
x_192 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_180, x_190);
lean_dec(x_180);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_193 = x_1;
} else {
 lean_dec_ref(x_1);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(5, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_190);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_191);
return x_195;
}
else
{
lean_object* x_196; 
lean_dec(x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_1);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_180);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_181);
if (x_197 == 0)
{
return x_181;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_181, 0);
x_199 = lean_ctor_get(x_181, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_181);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
default: 
{
lean_object* x_201; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_1);
lean_ctor_set(x_201, 1, x_9);
return x_201;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_mapFVarM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__1_spec__4(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__6(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__8(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__9(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__10(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__11(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_go_spec__12(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_apply_9(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_free_object(x_2);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_apply_9(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(8u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_shiftl(x_8, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = lean_st_mk_ref(x_7, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_mk_array(x_17, x_18);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_19);
x_21 = lean_st_mk_ref(x_13, x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box(0);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 0);
x_27 = lean_ctor_get(x_1, 4);
lean_inc(x_27);
lean_ctor_set(x_21, 1, x_7);
lean_ctor_set(x_21, 0, x_25);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_23);
x_28 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_spec__0(x_26, x_27, x_21, x_23, x_15, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_23, x_30);
lean_dec(x_23);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_15, x_32);
lean_dec(x_15);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 3);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_40 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_41 = lean_ctor_get(x_1, 5);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_29);
lean_ctor_set(x_42, 5, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*6, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*6 + 1, x_40);
x_43 = l_Lean_Compiler_LCNF_Decl_pullFunDecls(x_42, x_2, x_3, x_4, x_5, x_34);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
return x_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_28, 0);
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_28);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_box(0);
x_51 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 0);
x_52 = lean_ctor_get(x_1, 4);
lean_inc(x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_48);
x_54 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_spec__0(x_51, x_52, x_53, x_48, x_15, x_2, x_3, x_4, x_5, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_get(x_48, x_56);
lean_dec(x_48);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_get(x_15, x_58);
lean_dec(x_15);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 3);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_66 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_67 = lean_ctor_get(x_1, 5);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_55);
lean_ctor_set(x_68, 5, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*6 + 1, x_66);
x_69 = l_Lean_Compiler_LCNF_Decl_pullFunDecls(x_68, x_2, x_3, x_4, x_5, x_60);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_48);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_54, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_72 = x_54;
} else {
 lean_dec_ref(x_54);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_74 = lean_ctor_get(x_13, 0);
x_75 = lean_ctor_get(x_13, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_13);
x_76 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_77 = lean_box(0);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_mk_array(x_76, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_st_mk_ref(x_80, x_75);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_box(0);
x_86 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 0);
x_87 = lean_ctor_get(x_1, 4);
lean_inc(x_87);
if (lean_is_scalar(x_84)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_84;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_74);
lean_inc(x_82);
x_89 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointContextExtender_extend_spec__0(x_86, x_87, x_88, x_82, x_74, x_2, x_3, x_4, x_5, x_83);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_get(x_82, x_91);
lean_dec(x_82);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_st_ref_get(x_74, x_93);
lean_dec(x_74);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_1, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 3);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_101 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_102 = lean_ctor_get(x_1, 5);
lean_inc(x_102);
lean_dec(x_1);
x_103 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_97);
lean_ctor_set(x_103, 2, x_98);
lean_ctor_set(x_103, 3, x_99);
lean_ctor_set(x_103, 4, x_90);
lean_ctor_set(x_103, 5, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*6, x_100);
lean_ctor_set_uint8(x_103, sizeof(void*)*6 + 1, x_101);
x_104 = l_Lean_Compiler_LCNF_Decl_pullFunDecls(x_103, x_2, x_3, x_4, x_5, x_95);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_ctor_get(x_89, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_89, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_107 = x_89;
} else {
 lean_dec_ref(x_89);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instFVarIdSetInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_17; 
x_17 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(x_3, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_mk_string_unchecked("Lean.Data.RBMap", 15, 15);
x_19 = lean_mk_string_unchecked("Lean.RBMap.find!", 16, 16);
x_20 = lean_unsigned_to_nat(389u);
x_21 = lean_unsigned_to_nat(14u);
x_22 = lean_mk_string_unchecked("key is not in the map", 21, 21);
x_23 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_18, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
x_24 = l_panic___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__1(x_23);
x_5 = x_24;
goto block_16;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_5 = x_25;
goto block_16;
}
block_16:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_5, x_2);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(1);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___redArg(x_1, x_2, x_3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(x_9, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_11;
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_clearScope___redArg(x_4, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1___redArg___lam__0), 9, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at___Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1_spec__1___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_2, x_3);
if (x_17 == 0)
{
x_13 = x_12;
goto block_16;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_3, x_3);
if (x_18 == 0)
{
x_13 = x_12;
goto block_16;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_box(0);
x_20 = lean_usize_of_nat(x_2);
x_21 = lean_usize_of_nat(x_3);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___redArg(x_4, x_20, x_21, x_19, x_7, x_12);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_13 = x_23;
goto block_16;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lam__0___boxed), 12, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_10);
x_14 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1___redArg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_4);
lean_closure_set(x_7, 6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_1);
lean_closure_set(x_5, 3, lean_box(0));
lean_closure_set(x_5, 4, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__2), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_7);
lean_closure_set(x_8, 6, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__3), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_4);
lean_closure_set(x_7, 6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_apply_1(x_2, x_6);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, lean_box(0));
lean_closure_set(x_12, 4, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_1);
lean_closure_set(x_5, 3, lean_box(0));
lean_closure_set(x_5, 4, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__5), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, lean_box(0));
lean_closure_set(x_10, 4, lean_box(0));
lean_closure_set(x_10, 5, x_9);
lean_closure_set(x_10, 6, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__6), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_4);
lean_closure_set(x_7, 6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
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
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__8), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_5);
lean_closure_set(x_7, 6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_apply_1(x_2, x_6);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 5);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, lean_box(0));
lean_closure_set(x_12, 4, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__10), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_5);
lean_closure_set(x_7, 6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_14 = l_instMonadEIO(lean_box(0));
x_15 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
lean_inc(x_29);
lean_inc(x_26);
lean_inc(x_23);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_23);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_26);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_29);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_10);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
x_46 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_45);
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
lean_inc(x_47);
x_48 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__1), 5, 1);
lean_closure_set(x_48, 0, x_47);
lean_inc(x_47);
x_49 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__4), 5, 1);
lean_closure_set(x_49, 0, x_47);
lean_inc(x_47);
x_50 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__7), 5, 1);
lean_closure_set(x_50, 0, x_47);
lean_inc(x_47);
x_51 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__9), 5, 1);
lean_closure_set(x_51, 0, x_47);
lean_inc(x_47);
x_52 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1___lam__11), 5, 1);
lean_closure_set(x_52, 0, x_47);
x_53 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_47);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_51);
lean_inc(x_53);
x_55 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_50);
lean_ctor_set(x_56, 3, x_49);
lean_ctor_set(x_56, 4, x_48);
x_57 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_57, 0, lean_box(0));
lean_closure_set(x_57, 1, x_53);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_box(0);
x_60 = l_instInhabitedOfMonad___redArg(x_58, x_59);
x_61 = lean_panic_fn(x_60, x_1);
x_62 = lean_apply_8(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_62;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1(x_1, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_17;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_14 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_15 = lean_unsigned_to_nat(43u);
x_16 = lean_unsigned_to_nat(38u);
x_17 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_18 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_19 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_22 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_24; 
lean_dec(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_2 = x_21;
x_10 = x_24;
goto _start;
}
}
else
{
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_22;
}
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_30 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1___lam__0(x_1, x_26, x_27, x_28, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_26);
return x_30;
}
case 7:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_35 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1___lam__0(x_1, x_31, x_32, x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_31);
return x_35;
}
case 8:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_37 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_38 = lean_unsigned_to_nat(43u);
x_39 = lean_unsigned_to_nat(38u);
x_40 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_41 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_36, x_37, x_38, x_39, x_40);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
x_42 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_42;
}
case 11:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_44 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_45 = lean_unsigned_to_nat(43u);
x_46 = lean_unsigned_to_nat(38u);
x_47 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_48 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_43, x_44, x_45, x_46, x_47);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_43);
x_49 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1_spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_49;
}
default: 
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_10);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_apply_9(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_allFVarM_go___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0___lam__0), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = lean_box(1);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___boxed), 10, 1);
lean_closure_set(x_18, 0, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_17);
x_19 = l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0(x_18, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_28 = lean_unbox(x_20);
lean_dec(x_20);
if (x_28 == 0)
{
lean_dec(x_17);
lean_dec(x_16);
x_22 = x_5;
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; size_t x_44; size_t x_45; lean_object* x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = l_Lean_Compiler_LCNF_Arg_toExpr(x_17);
x_34 = lean_array_get_size(x_31);
x_35 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_32);
x_36 = lean_unsigned_to_nat(32u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_unsigned_to_nat(16u);
x_41 = lean_uint64_of_nat(x_40);
x_42 = lean_uint64_shift_right(x_39, x_41);
x_43 = lean_uint64_xor(x_39, x_42);
x_44 = lean_uint64_to_usize(x_43);
x_45 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_usize_of_nat(x_46);
x_48 = lean_usize_sub(x_45, x_47);
x_49 = lean_usize_land(x_44, x_48);
x_50 = lean_array_uget(x_31, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_32, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_nat_add(x_30, x_46);
lean_dec(x_30);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_32);
lean_ctor_set(x_53, 1, x_33);
lean_ctor_set(x_53, 2, x_50);
x_54 = lean_array_uset(x_31, x_49, x_53);
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
lean_object* x_61; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_54);
lean_ctor_set(x_5, 1, x_61);
lean_ctor_set(x_5, 0, x_52);
x_22 = x_5;
goto block_27;
}
else
{
lean_ctor_set(x_5, 1, x_54);
lean_ctor_set(x_5, 0, x_52);
x_22 = x_5;
goto block_27;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_box(0);
x_63 = lean_array_uset(x_31, x_49, x_62);
x_64 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_32, x_33, x_50);
x_65 = lean_array_uset(x_63, x_49, x_64);
lean_ctor_set(x_5, 1, x_65);
x_22 = x_5;
goto block_27;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; size_t x_80; size_t x_81; lean_object* x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; uint8_t x_87; 
x_66 = lean_ctor_get(x_5, 0);
x_67 = lean_ctor_get(x_5, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_5);
x_68 = lean_ctor_get(x_16, 0);
lean_inc(x_68);
lean_dec(x_16);
x_69 = l_Lean_Compiler_LCNF_Arg_toExpr(x_17);
x_70 = lean_array_get_size(x_67);
x_71 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_68);
x_72 = lean_unsigned_to_nat(32u);
x_73 = lean_uint64_of_nat(x_72);
x_74 = lean_uint64_shift_right(x_71, x_73);
x_75 = lean_uint64_xor(x_71, x_74);
x_76 = lean_unsigned_to_nat(16u);
x_77 = lean_uint64_of_nat(x_76);
x_78 = lean_uint64_shift_right(x_75, x_77);
x_79 = lean_uint64_xor(x_75, x_78);
x_80 = lean_uint64_to_usize(x_79);
x_81 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_usize_of_nat(x_82);
x_84 = lean_usize_sub(x_81, x_83);
x_85 = lean_usize_land(x_80, x_84);
x_86 = lean_array_uget(x_67, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_68, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_88 = lean_nat_add(x_66, x_82);
lean_dec(x_66);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_68);
lean_ctor_set(x_89, 1, x_69);
lean_ctor_set(x_89, 2, x_86);
x_90 = lean_array_uset(x_67, x_85, x_89);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_nat_shiftl(x_88, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_97);
x_22 = x_98;
goto block_27;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_90);
x_22 = x_99;
goto block_27;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_67, x_85, x_100);
x_102 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_68, x_69, x_86);
x_103 = lean_array_uset(x_101, x_85, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_66);
lean_ctor_set(x_104, 1, x_103);
x_22 = x_104;
goto block_27;
}
}
}
block_27:
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_5 = x_22;
x_13 = x_21;
goto _start;
}
}
else
{
uint8_t x_105; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_19);
if (x_105 == 0)
{
return x_19;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_19, 0);
x_107 = lean_ctor_get(x_19, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_19);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_5);
lean_ctor_set(x_109, 1, x_13);
return x_109;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; lean_object* x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_array_get_size(x_19);
x_22 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_20);
x_23 = lean_unsigned_to_nat(32u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_shift_right(x_22, x_24);
x_26 = lean_uint64_xor(x_22, x_25);
x_27 = lean_unsigned_to_nat(16u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_sub(x_32, x_34);
x_36 = lean_usize_land(x_31, x_35);
x_37 = lean_array_uget(x_19, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_20, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_6 = x_4;
x_7 = x_5;
goto block_12;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Compiler_LCNF_Arg_toExpr(x_17);
x_41 = lean_expr_eqv(x_40, x_39);
lean_dec(x_39);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_20, x_37);
if (x_42 == 0)
{
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_6 = x_4;
x_7 = x_5;
goto block_12;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_4, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_4, 0);
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = lean_array_uset(x_19, x_36, x_46);
x_48 = lean_nat_sub(x_18, x_33);
lean_dec(x_18);
x_49 = l_Std_DHashMap_Internal_AssocList_erase___at___Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(x_20, x_37);
lean_dec(x_20);
x_50 = lean_array_uset(x_47, x_36, x_49);
lean_ctor_set(x_4, 1, x_50);
lean_ctor_set(x_4, 0, x_48);
x_6 = x_4;
x_7 = x_5;
goto block_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
x_51 = lean_box(0);
x_52 = lean_array_uset(x_19, x_36, x_51);
x_53 = lean_nat_sub(x_18, x_33);
lean_dec(x_18);
x_54 = l_Std_DHashMap_Internal_AssocList_erase___at___Lean_Compiler_LCNF_LCtx_eraseParam_spec__0___redArg(x_20, x_37);
lean_dec(x_20);
x_55 = lean_array_uset(x_52, x_36, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_6 = x_56;
x_7 = x_5;
goto block_12;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_6 = x_4;
x_7 = x_5;
goto block_12;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___redArg(x_1, x_2, x_3, x_4, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_19; 
x_19 = lean_nat_dec_lt(x_2, x_3);
if (x_19 == 0)
{
x_13 = x_12;
goto block_18;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_3, x_3);
if (x_20 == 0)
{
x_13 = x_12;
goto block_18;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_box(0);
x_22 = lean_usize_of_nat(x_2);
x_23 = lean_usize_of_nat(x_3);
x_24 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___redArg(x_4, x_22, x_23, x_21, x_7, x_12);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_13 = x_25;
goto block_18;
}
}
block_18:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_13);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
x_15 = l_Lean_Compiler_LCNF_AltCore_getParams(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7___lam__0___boxed), 12, 4);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__1___redArg(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_20;
x_12 = x_21;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(x_12, x_4, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_1 = x_11;
x_9 = x_14;
goto _start;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
x_18 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(x_20, x_4, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_1 = x_17;
x_9 = x_22;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_26 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Compiler_LCNF_ScopeM_getScope___redArg(x_4, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
lean_inc(x_31);
x_32 = l_Lean_Compiler_LCNF_ScopeM_addToScope___redArg(x_31, x_4, x_30);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_31, x_29);
x_1 = x_25;
x_2 = x_34;
x_9 = x_33;
goto _start;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_52; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
lean_inc(x_36);
x_52 = l_Lean_Compiler_LCNF_getFunDecl(x_36, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_get(x_3, x_54);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(x_57, x_36);
lean_dec(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_60 = lean_unsigned_to_nat(8u);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_shiftl(x_60, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = l_Nat_nextPowerOfTwo(x_65);
lean_dec(x_65);
x_67 = lean_box(0);
x_68 = lean_mk_array(x_66, x_67);
lean_ctor_set(x_55, 1, x_68);
lean_ctor_set(x_55, 0, x_61);
x_69 = lean_ctor_get(x_53, 2);
lean_inc(x_69);
lean_dec(x_53);
x_70 = l_Array_zip___redArg(x_69, x_37);
lean_dec(x_37);
lean_dec(x_69);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_61, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_38 = x_55;
x_39 = x_58;
goto block_51;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_71, x_71);
if (x_73 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_38 = x_55;
x_39 = x_58;
goto block_51;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; 
x_74 = lean_usize_of_nat(x_61);
x_75 = lean_usize_of_nat(x_71);
lean_dec(x_71);
lean_inc(x_3);
lean_inc(x_36);
x_76 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__5(x_36, x_70, x_74, x_75, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_70);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_38 = x_77;
x_39 = x_78;
goto block_51;
}
else
{
uint8_t x_79; 
lean_dec(x_36);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_76);
if (x_79 == 0)
{
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_76);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; lean_object* x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_free_object(x_55);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_83 = lean_ctor_get(x_59, 0);
lean_inc(x_83);
lean_dec(x_59);
x_84 = lean_ctor_get(x_53, 2);
lean_inc(x_84);
lean_dec(x_53);
x_85 = l_Array_zip___redArg(x_84, x_37);
lean_dec(x_37);
lean_dec(x_84);
x_86 = lean_array_size(x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_usize_of_nat(x_87);
x_89 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___redArg(x_85, x_86, x_88, x_83, x_58);
lean_dec(x_85);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_take(x_3, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_93, x_36, x_90);
x_96 = lean_st_ref_set(x_3, x_95, x_94);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_dec(x_98);
x_99 = lean_box(0);
lean_ctor_set(x_96, 0, x_99);
return x_96;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_55, 0);
x_104 = lean_ctor_get(x_55, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_55);
x_105 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(x_103, x_36);
lean_dec(x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_106 = lean_unsigned_to_nat(8u);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_unsigned_to_nat(2u);
x_109 = lean_nat_shiftl(x_106, x_108);
x_110 = lean_unsigned_to_nat(3u);
x_111 = lean_nat_div(x_109, x_110);
lean_dec(x_109);
x_112 = l_Nat_nextPowerOfTwo(x_111);
lean_dec(x_111);
x_113 = lean_box(0);
x_114 = lean_mk_array(x_112, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_ctor_get(x_53, 2);
lean_inc(x_116);
lean_dec(x_53);
x_117 = l_Array_zip___redArg(x_116, x_37);
lean_dec(x_37);
lean_dec(x_116);
x_118 = lean_array_get_size(x_117);
x_119 = lean_nat_dec_lt(x_107, x_118);
if (x_119 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_38 = x_115;
x_39 = x_104;
goto block_51;
}
else
{
uint8_t x_120; 
x_120 = lean_nat_dec_le(x_118, x_118);
if (x_120 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_38 = x_115;
x_39 = x_104;
goto block_51;
}
else
{
size_t x_121; size_t x_122; lean_object* x_123; 
x_121 = lean_usize_of_nat(x_107);
x_122 = lean_usize_of_nat(x_118);
lean_dec(x_118);
lean_inc(x_3);
lean_inc(x_36);
x_123 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__5(x_36, x_117, x_121, x_122, x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_117);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_38 = x_124;
x_39 = x_125;
goto block_51;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_36);
lean_dec(x_3);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_128 = x_123;
} else {
 lean_dec_ref(x_123);
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
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; size_t x_133; lean_object* x_134; size_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_130 = lean_ctor_get(x_105, 0);
lean_inc(x_130);
lean_dec(x_105);
x_131 = lean_ctor_get(x_53, 2);
lean_inc(x_131);
lean_dec(x_53);
x_132 = l_Array_zip___redArg(x_131, x_37);
lean_dec(x_37);
lean_dec(x_131);
x_133 = lean_array_size(x_132);
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_usize_of_nat(x_134);
x_136 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___redArg(x_132, x_133, x_135, x_130, x_104);
lean_dec(x_132);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_st_ref_take(x_3, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_140, x_36, x_137);
x_143 = lean_st_ref_set(x_3, x_142, x_141);
lean_dec(x_3);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_52);
if (x_148 == 0)
{
return x_52;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_52, 0);
x_150 = lean_ctor_get(x_52, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_52);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
block_51:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_st_ref_take(x_3, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_41, x_36, x_38);
x_44 = lean_st_ref_set(x_3, x_43, x_42);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
case 4:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_1, 0);
lean_inc(x_152);
lean_dec(x_1);
x_153 = lean_ctor_get(x_152, 3);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_array_get_size(x_153);
x_156 = lean_box(0);
x_157 = lean_nat_dec_lt(x_154, x_155);
if (x_157 == 0)
{
lean_object* x_158; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_9);
return x_158;
}
else
{
uint8_t x_159; 
x_159 = lean_nat_dec_le(x_155, x_155);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_9);
return x_160;
}
else
{
size_t x_161; size_t x_162; lean_object* x_163; 
x_161 = lean_usize_of_nat(x_154);
x_162 = lean_usize_of_nat(x_155);
lean_dec(x_155);
x_163 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7(x_153, x_161, x_162, x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_153);
return x_163;
}
}
}
default: 
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_9);
return x_165;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__0_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__5(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__6(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze_spec__7(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_9 = x_23;
goto block_22;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_9 = x_24;
goto block_22;
}
block_22:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_3, x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_29; lean_object* x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; lean_object* x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; uint8_t x_47; 
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_array_uget(x_2, x_3);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
x_30 = lean_array_get_size(x_20);
x_31 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_29);
x_32 = lean_unsigned_to_nat(32u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_unsigned_to_nat(16u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_usize_of_nat(x_42);
x_44 = lean_usize_sub(x_41, x_43);
x_45 = lean_usize_land(x_40, x_44);
x_46 = lean_array_uget(x_20, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_29, x_46);
lean_dec(x_46);
lean_dec(x_29);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___lam__0(x_47, x_19, x_48, x_6, x_7, x_8, x_9, x_10, x_11);
x_22 = x_49;
goto block_28;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_Compiler_LCNF_eraseParam(x_21, x_7, x_8, x_9, x_10, x_11);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___lam__0(x_47, x_19, x_51, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_51);
x_22 = x_53;
goto block_28;
}
block_28:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_12 = x_5;
x_13 = x_25;
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_array_push(x_5, x_21);
x_12 = x_27;
x_13 = x_26;
goto block_18;
}
}
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_5);
lean_ctor_set(x_54, 1, x_11);
return x_54;
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_array_uget(x_2, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_get_size(x_13);
x_18 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_16);
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
x_33 = lean_array_uget(x_13, x_32);
x_34 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_16, x_33);
lean_dec(x_33);
lean_dec(x_16);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_array_push(x_5, x_14);
x_6 = x_35;
goto block_11;
}
else
{
lean_dec(x_14);
x_6 = x_5;
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
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_instBEqFVarId;
x_3 = l_Lean_instHashableFVarId;
x_4 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_3);
x_5 = lean_panic_fn(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce), 7, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_AltCore_mapCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__0(x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_18, x_2, x_15);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_17, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; size_t x_31; size_t x_32; uint8_t x_33; 
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
x_31 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_32 = lean_ptr_addr(x_19);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
x_22 = x_33;
goto block_30;
}
else
{
size_t x_34; uint8_t x_35; 
x_34 = lean_ptr_addr(x_16);
x_35 = lean_usize_dec_eq(x_34, x_34);
x_22 = x_35;
goto block_30;
}
block_30:
{
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
lean_ctor_set(x_1, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_21;
}
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_19);
if (lean_is_scalar(x_21)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_21;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_16);
if (lean_is_scalar(x_21)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_21;
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_20);
return x_29;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
return x_18;
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 4);
lean_inc(x_38);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_38, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_36, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 2);
lean_inc(x_43);
lean_inc(x_36);
x_44 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_36, x_42, x_43, x_40, x_4, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_37);
x_47 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_37, x_2, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; size_t x_60; size_t x_61; uint8_t x_62; 
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
x_60 = lean_ptr_addr(x_37);
lean_dec(x_37);
x_61 = lean_ptr_addr(x_48);
x_62 = lean_usize_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_dec(x_36);
x_51 = x_62;
goto block_59;
}
else
{
size_t x_63; size_t x_64; uint8_t x_65; 
x_63 = lean_ptr_addr(x_36);
lean_dec(x_36);
x_64 = lean_ptr_addr(x_45);
x_65 = lean_usize_dec_eq(x_63, x_64);
x_51 = x_65;
goto block_59;
}
block_59:
{
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_1);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_1, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_1, 0);
lean_dec(x_54);
lean_ctor_set(x_1, 1, x_48);
lean_ctor_set(x_1, 0, x_45);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_48);
if (lean_is_scalar(x_50)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_50;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_48);
lean_dec(x_45);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_50;
}
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
}
else
{
lean_dec(x_45);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_1);
return x_47;
}
}
else
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_39;
}
}
case 2:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_90; lean_object* x_91; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
x_91 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(x_2, x_90);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
lean_inc(x_67);
x_92 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_67, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; size_t x_105; size_t x_106; uint8_t x_107; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_105 = lean_ptr_addr(x_67);
lean_dec(x_67);
x_106 = lean_ptr_addr(x_93);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
x_96 = x_107;
goto block_104;
}
else
{
size_t x_108; uint8_t x_109; 
x_108 = lean_ptr_addr(x_66);
x_109 = lean_usize_dec_eq(x_108, x_108);
x_96 = x_109;
goto block_104;
}
block_104:
{
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_1);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_1, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_1, 0);
lean_dec(x_99);
lean_ctor_set(x_1, 1, x_93);
if (lean_is_scalar(x_95)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_95;
}
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_94);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_1);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_66);
lean_ctor_set(x_101, 1, x_93);
if (lean_is_scalar(x_95)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_95;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_94);
return x_102;
}
}
else
{
lean_object* x_103; 
lean_dec(x_93);
lean_dec(x_66);
if (lean_is_scalar(x_95)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_95;
}
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_94);
return x_103;
}
}
}
else
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_1);
return x_92;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_143; uint8_t x_144; 
x_110 = lean_ctor_get(x_91, 0);
lean_inc(x_110);
lean_dec(x_91);
x_111 = lean_ctor_get(x_66, 2);
lean_inc(x_111);
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_array_get_size(x_111);
x_143 = lean_mk_empty_array_with_capacity(x_112);
x_144 = lean_nat_dec_lt(x_112, x_113);
if (x_144 == 0)
{
lean_dec(x_111);
x_114 = x_143;
x_115 = x_7;
goto block_142;
}
else
{
uint8_t x_145; 
x_145 = lean_nat_dec_le(x_113, x_113);
if (x_145 == 0)
{
lean_dec(x_111);
x_114 = x_143;
x_115 = x_7;
goto block_142;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_usize_of_nat(x_112);
x_147 = lean_usize_of_nat(x_113);
x_148 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1(x_110, x_111, x_146, x_147, x_143, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_111);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_114 = x_149;
x_115 = x_150;
goto block_142;
}
}
block_142:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_66, 4);
lean_inc(x_116);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_117 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_116, x_2, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_box(0);
x_121 = lean_unbox(x_120);
x_122 = l_Lean_Compiler_LCNF_normCodeImp(x_121, x_118, x_110, x_3, x_4, x_5, x_6, x_119);
lean_dec(x_110);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_array_get_size(x_114);
x_126 = lean_nat_dec_eq(x_125, x_113);
lean_dec(x_113);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
lean_inc(x_123);
x_127 = l_Lean_Compiler_LCNF_Code_inferType(x_123, x_3, x_4, x_5, x_6, x_124);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_114);
x_130 = l_Lean_Compiler_LCNF_mkForallParams(x_114, x_128, x_3, x_4, x_5, x_6, x_129);
lean_dec(x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_68 = x_114;
x_69 = x_123;
x_70 = x_131;
x_71 = x_2;
x_72 = x_3;
x_73 = x_4;
x_74 = x_5;
x_75 = x_6;
x_76 = x_132;
goto block_89;
}
else
{
uint8_t x_133; 
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_130);
if (x_133 == 0)
{
return x_130;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_130, 0);
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_130);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_123);
lean_dec(x_114);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_127);
if (x_137 == 0)
{
return x_127;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_127, 0);
x_139 = lean_ctor_get(x_127, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_127);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_66, 3);
lean_inc(x_141);
x_68 = x_114;
x_69 = x_123;
x_70 = x_141;
x_71 = x_2;
x_72 = x_3;
x_73 = x_4;
x_74 = x_5;
x_75 = x_6;
x_76 = x_124;
goto block_89;
}
}
else
{
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_110);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_117;
}
}
}
block_89:
{
lean_object* x_77; 
lean_inc(x_73);
lean_inc(x_67);
x_77 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_67, x_71, x_72, x_73, x_74, x_75, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_66);
x_80 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_66, x_70, x_68, x_69, x_73, x_79);
lean_dec(x_73);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ptr_addr(x_67);
lean_dec(x_67);
x_84 = lean_ptr_addr(x_78);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_dec(x_66);
x_8 = x_82;
x_9 = x_81;
x_10 = x_78;
x_11 = x_85;
goto block_15;
}
else
{
size_t x_86; size_t x_87; uint8_t x_88; 
x_86 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_87 = lean_ptr_addr(x_81);
x_88 = lean_usize_dec_eq(x_86, x_87);
x_8 = x_82;
x_9 = x_81;
x_10 = x_78;
x_11 = x_88;
goto block_15;
}
}
else
{
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_1);
return x_77;
}
}
}
case 3:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_164; lean_object* x_165; lean_object* x_175; lean_object* x_194; 
x_151 = lean_ctor_get(x_1, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_1, 1);
lean_inc(x_152);
x_194 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope_spec__0___redArg(x_2, x_151);
lean_dec(x_2);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = lean_mk_string_unchecked("Lean.Data.RBMap", 15, 15);
x_196 = lean_mk_string_unchecked("Lean.RBMap.find!", 16, 16);
x_197 = lean_unsigned_to_nat(389u);
x_198 = lean_unsigned_to_nat(14u);
x_199 = lean_mk_string_unchecked("key is not in the map", 21, 21);
x_200 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_195, x_196, x_197, x_198, x_199);
lean_dec(x_199);
lean_dec(x_196);
lean_dec(x_195);
x_201 = l_panic___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__4(x_200);
x_175 = x_201;
goto block_193;
}
else
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_194, 0);
lean_inc(x_202);
lean_dec(x_194);
x_175 = x_202;
goto block_193;
}
block_163:
{
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_1);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_1, 1);
lean_dec(x_157);
x_158 = lean_ctor_get(x_1, 0);
lean_dec(x_158);
lean_ctor_set(x_1, 1, x_153);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_1);
lean_ctor_set(x_159, 1, x_154);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_1);
x_160 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_153);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_154);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_153);
lean_dec(x_151);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_1);
lean_ctor_set(x_162, 1, x_154);
return x_162;
}
}
block_174:
{
size_t x_166; lean_object* x_167; size_t x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_array_size(x_165);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_usize_of_nat(x_167);
x_169 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__2(x_166, x_168, x_165);
x_170 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_151, x_151);
if (x_170 == 0)
{
lean_dec(x_152);
x_153 = x_169;
x_154 = x_164;
x_155 = x_170;
goto block_163;
}
else
{
size_t x_171; size_t x_172; uint8_t x_173; 
x_171 = lean_ptr_addr(x_152);
lean_dec(x_152);
x_172 = lean_ptr_addr(x_169);
x_173 = lean_usize_dec_eq(x_171, x_172);
x_153 = x_169;
x_154 = x_164;
x_155 = x_173;
goto block_163;
}
}
block_193:
{
lean_object* x_176; 
lean_inc(x_151);
x_176 = l_Lean_Compiler_LCNF_getFunDecl(x_151, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 2);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Array_zip___redArg(x_179, x_152);
lean_dec(x_179);
x_181 = lean_unsigned_to_nat(0u);
x_182 = lean_array_get_size(x_180);
x_183 = lean_mk_empty_array_with_capacity(x_181);
x_184 = lean_nat_dec_lt(x_181, x_182);
if (x_184 == 0)
{
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_175);
x_164 = x_178;
x_165 = x_183;
goto block_174;
}
else
{
uint8_t x_185; 
x_185 = lean_nat_dec_le(x_182, x_182);
if (x_185 == 0)
{
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_175);
x_164 = x_178;
x_165 = x_183;
goto block_174;
}
else
{
size_t x_186; size_t x_187; lean_object* x_188; 
x_186 = lean_usize_of_nat(x_181);
x_187 = lean_usize_of_nat(x_182);
lean_dec(x_182);
x_188 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__3(x_175, x_180, x_186, x_187, x_183);
lean_dec(x_180);
lean_dec(x_175);
x_164 = x_178;
x_165 = x_188;
goto block_174;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_175);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_176);
if (x_189 == 0)
{
return x_176;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_176, 0);
x_191 = lean_ctor_get(x_176, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_176);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
case 4:
{
lean_object* x_203; lean_object* x_204; size_t x_205; lean_object* x_206; size_t x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_1, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_203, 3);
lean_inc(x_204);
x_205 = lean_array_size(x_204);
x_206 = lean_unsigned_to_nat(0u);
x_207 = lean_usize_of_nat(x_206);
lean_inc(x_204);
x_208 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__5(x_205, x_207, x_204, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_219; size_t x_223; size_t x_224; uint8_t x_225; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_203, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_203, 2);
lean_inc(x_213);
x_223 = lean_ptr_addr(x_204);
lean_dec(x_204);
x_224 = lean_ptr_addr(x_209);
x_225 = lean_usize_dec_eq(x_223, x_224);
if (x_225 == 0)
{
x_219 = x_225;
goto block_222;
}
else
{
size_t x_226; uint8_t x_227; 
x_226 = lean_ptr_addr(x_212);
x_227 = lean_usize_dec_eq(x_226, x_226);
x_219 = x_227;
goto block_222;
}
block_218:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_203, 0);
lean_inc(x_214);
lean_dec(x_203);
x_215 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_209);
x_216 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_216, 0, x_215);
if (lean_is_scalar(x_211)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_211;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_210);
return x_217;
}
block_222:
{
if (x_219 == 0)
{
lean_dec(x_1);
goto block_218;
}
else
{
uint8_t x_220; 
x_220 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_213, x_213);
if (x_220 == 0)
{
lean_dec(x_1);
goto block_218;
}
else
{
lean_object* x_221; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_203);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_1);
lean_ctor_set(x_221, 1, x_210);
return x_221;
}
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_208);
if (x_228 == 0)
{
return x_208;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_208, 0);
x_230 = lean_ctor_get(x_208, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_208);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
default: 
{
lean_object* x_232; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_1);
lean_ctor_set(x_232, 1, x_7);
return x_232;
}
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___lam__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce_spec__5(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
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
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_box(0);
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_mk_ref(x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze), 9, 0);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
lean_inc(x_12);
lean_inc(x_15);
x_16 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_spec__0(x_14, x_15, x_7, x_12, x_9, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_12, x_17);
lean_dec(x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_9, x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce), 7, 0);
x_24 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_spec__1(x_23, x_15, x_19, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 3);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_33 = lean_ctor_get(x_1, 5);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_26);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*6, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*6 + 1, x_32);
lean_ctor_set(x_24, 0, x_34);
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 3);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_42 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_43 = lean_ctor_get(x_1, 5);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_38);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_35);
lean_ctor_set(x_44, 5, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*6 + 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___redArg(x_1, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
lean_inc(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
lean_inc(x_19);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_19);
x_26 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set(x_26, 5, x_22);
lean_ctor_set(x_26, 6, x_23);
lean_ctor_set(x_26, 7, x_24);
lean_ctor_set(x_26, 8, x_25);
x_27 = lean_st_ref_take(x_5, x_13);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_17);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_16);
lean_ctor_set(x_31, 3, x_17);
x_32 = lean_ctor_get(x_4, 5);
lean_ctor_set_tag(x_27, 3);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 0, x_31);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 3);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_36, sizeof(void*)*1);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_float_of_nat(x_18);
x_40 = lean_box(0);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_float(x_42, sizeof(void*)*2, x_39);
lean_ctor_set_float(x_42, sizeof(void*)*2 + 8, x_39);
x_43 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_43);
x_44 = lean_mk_empty_array_with_capacity(x_18);
x_45 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_27);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_32);
lean_ctor_set(x_10, 1, x_45);
lean_ctor_set(x_10, 0, x_32);
x_46 = l_Lean_PersistentArray_push___redArg(x_38, x_10);
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_37);
x_48 = lean_ctor_get(x_29, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_29, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_29, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_29, 7);
lean_inc(x_51);
lean_dec(x_29);
x_52 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_34);
lean_ctor_set(x_52, 2, x_35);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_48);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set(x_52, 6, x_50);
lean_ctor_set(x_52, 7, x_51);
x_53 = lean_st_ref_set(x_5, x_52, x_30);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; double x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_60 = lean_ctor_get(x_27, 0);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_27);
lean_inc(x_17);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_26);
lean_ctor_set(x_62, 2, x_16);
lean_ctor_set(x_62, 3, x_17);
x_63 = lean_ctor_get(x_4, 5);
x_64 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_2);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_60, 3);
lean_inc(x_68);
x_69 = lean_ctor_get_uint64(x_68, sizeof(void*)*1);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_float_of_nat(x_18);
x_72 = lean_box(0);
x_73 = lean_mk_string_unchecked("", 0, 0);
x_74 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_float(x_74, sizeof(void*)*2, x_71);
lean_ctor_set_float(x_74, sizeof(void*)*2 + 8, x_71);
x_75 = lean_unbox(x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*2 + 16, x_75);
x_76 = lean_mk_empty_array_with_capacity(x_18);
x_77 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_64);
lean_ctor_set(x_77, 2, x_76);
lean_inc(x_63);
lean_ctor_set(x_10, 1, x_77);
lean_ctor_set(x_10, 0, x_63);
x_78 = l_Lean_PersistentArray_push___redArg(x_70, x_10);
x_79 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint64(x_79, sizeof(void*)*1, x_69);
x_80 = lean_ctor_get(x_60, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_60, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_60, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_60, 7);
lean_inc(x_83);
lean_dec(x_60);
x_84 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_84, 0, x_65);
lean_ctor_set(x_84, 1, x_66);
lean_ctor_set(x_84, 2, x_67);
lean_ctor_set(x_84, 3, x_79);
lean_ctor_set(x_84, 4, x_80);
lean_ctor_set(x_84, 5, x_81);
lean_ctor_set(x_84, 6, x_82);
lean_ctor_set(x_84, 7, x_83);
x_85 = lean_st_ref_set(x_5, x_84, x_61);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint64_t x_116; lean_object* x_117; double x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_90 = lean_ctor_get(x_10, 0);
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_10);
x_92 = lean_ctor_get(x_8, 0);
lean_inc(x_92);
lean_dec(x_8);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_94 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_93);
lean_dec(x_93);
x_95 = lean_ctor_get(x_4, 2);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_97);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
lean_inc(x_97);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_97);
lean_inc(x_97);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_97);
lean_inc(x_97);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_97);
lean_inc(x_97);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_97);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_97);
x_104 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_96);
lean_ctor_set(x_104, 2, x_96);
lean_ctor_set(x_104, 3, x_98);
lean_ctor_set(x_104, 4, x_99);
lean_ctor_set(x_104, 5, x_100);
lean_ctor_set(x_104, 6, x_101);
lean_ctor_set(x_104, 7, x_102);
lean_ctor_set(x_104, 8, x_103);
x_105 = lean_st_ref_take(x_5, x_91);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
lean_inc(x_95);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_92);
lean_ctor_set(x_109, 1, x_104);
lean_ctor_set(x_109, 2, x_94);
lean_ctor_set(x_109, 3, x_95);
x_110 = lean_ctor_get(x_4, 5);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(3, 2, 0);
} else {
 x_111 = x_108;
 lean_ctor_set_tag(x_111, 3);
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_2);
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_106, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_106, 3);
lean_inc(x_115);
x_116 = lean_ctor_get_uint64(x_115, sizeof(void*)*1);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_float_of_nat(x_96);
x_119 = lean_box(0);
x_120 = lean_mk_string_unchecked("", 0, 0);
x_121 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_121, 0, x_1);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set_float(x_121, sizeof(void*)*2, x_118);
lean_ctor_set_float(x_121, sizeof(void*)*2 + 8, x_118);
x_122 = lean_unbox(x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*2 + 16, x_122);
x_123 = lean_mk_empty_array_with_capacity(x_96);
x_124 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_124, 2, x_123);
lean_inc(x_110);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_110);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_PersistentArray_push___redArg(x_117, x_125);
x_127 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set_uint64(x_127, sizeof(void*)*1, x_116);
x_128 = lean_ctor_get(x_106, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_106, 5);
lean_inc(x_129);
x_130 = lean_ctor_get(x_106, 6);
lean_inc(x_130);
x_131 = lean_ctor_get(x_106, 7);
lean_inc(x_131);
lean_dec(x_106);
x_132 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_132, 0, x_112);
lean_ctor_set(x_132, 1, x_113);
lean_ctor_set(x_132, 2, x_114);
lean_ctor_set(x_132, 3, x_127);
lean_ctor_set(x_132, 4, x_128);
lean_ctor_set(x_132, 5, x_129);
lean_ctor_set(x_132, 6, x_130);
lean_ctor_set(x_132, 7, x_131);
x_133 = lean_st_ref_set(x_5, x_132, x_107);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
x_136 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_JoinPointFinder_find(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("Compiler", 8, 8);
x_11 = lean_mk_string_unchecked("findJoinPoints", 14, 14);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
lean_inc(x_12);
x_13 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___redArg(x_12, x_4, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Compiler_LCNF_JoinPointFinder_replace(x_1, x_8, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_8);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_mk_string_unchecked("Found: ", 7, 7);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_24);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_22);
x_28 = lean_mk_string_unchecked(" jp candidates", 14, 14);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___redArg(x_12, x_30, x_3, x_4, x_5, x_19);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Compiler_LCNF_JoinPointFinder_replace(x_1, x_8, x_2, x_3, x_4, x_5, x_32);
lean_dec(x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_mk_string_unchecked("Found: ", 7, 7);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Init_Data_Repr_0__Nat_reprFast(x_38);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_MessageData_ofFormat(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked(" jp candidates", 14, 14);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___redArg(x_12, x_45, x_3, x_4, x_5, x_34);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Compiler_LCNF_JoinPointFinder_replace(x_1, x_8, x_2, x_3, x_4, x_5, x_47);
lean_dec(x_8);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_7);
if (x_49 == 0)
{
return x_7;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_7);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_findJoinPoints_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_findJoinPoints() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("findJoinPoints", 14, 14);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_findJoinPoints), 6, 0);
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4936_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("findJoinPoints", 14, 14);
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
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("JoinPoints", 10, 10);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(4936u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extendJoinPointContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5005_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_12 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("optConfig", 9, 9);
x_17 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_16);
lean_inc(x_7);
lean_inc(x_11);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_7);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_array_push(x_15, x_20);
lean_inc(x_18);
x_22 = lean_array_push(x_21, x_18);
lean_inc(x_18);
x_23 = lean_array_push(x_22, x_18);
lean_inc(x_18);
x_24 = lean_array_push(x_23, x_18);
x_25 = lean_array_push(x_24, x_18);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_7);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_array_push(x_7, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_extendJoinPointContext___redArg___lam__0), 6, 0);
x_4 = lean_mk_string_unchecked("extendJoinPointContext", 22, 22);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_5, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Compiler_LCNF_extendJoinPointContext(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5019_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("extendJoinPointContext", 22, 22);
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
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("JoinPoints", 10, 10);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(5019u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_commonJoinPointArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_commonJoinPointArgs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_commonJoinPointArgs___lam__0), 6, 0);
x_2 = lean_mk_string_unchecked("commonJoinPointArgs", 19, 19);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_3, x_1, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5087_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("commonJoinPointArgs", 19, 19);
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
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("JoinPoints", 10, 10);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(5087u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
return x_26;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ScopeM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_JoinPoints(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullFunDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ScopeM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo = _init_l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo);
l_Lean_Compiler_LCNF_findJoinPoints = _init_l_Lean_Compiler_LCNF_findJoinPoints();
lean_mark_persistent(l_Lean_Compiler_LCNF_findJoinPoints);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4936_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5005_ = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5005_();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5005_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5019_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_commonJoinPointArgs = _init_l_Lean_Compiler_LCNF_commonJoinPointArgs();
lean_mark_persistent(l_Lean_Compiler_LCNF_commonJoinPointArgs);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5087_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
