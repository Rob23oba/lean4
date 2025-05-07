// Lean compiler output
// Module: Lean.Compiler.LCNF.ToLCNF
// Imports: Lean.ProjFns Lean.Meta.CtorRecognizer Lean.Compiler.BorrowedAnnotation Lean.Compiler.CSimpAttr Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Util
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
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__3___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_get_implemented_by(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCtorArity_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_marked_borrowed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_csimp_replace_constants(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t lean_is_no_confusion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_RBNode_erase___at___Lean_LocalContext_erase_spec__1___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CasesInfo_numAlts(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isRuntimeBultinType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letFunAppArgs_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_GetElem_0__List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_get_projection_info(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("lcProof", 7, 7);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("lcProof", 7, 7);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = l_Lean_Expr_app___override(x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = l_Array_empty(lean_box(0));
x_3 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
lean_inc(x_2);
x_7 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(x_1, x_3, x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 4)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_10, 1);
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_dec(x_20);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_free_object(x_10);
x_1 = x_20;
x_6 = x_18;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
x_1 = x_27;
x_6 = x_26;
goto _start;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_10, 0);
lean_dec(x_35);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_array_uget(x_13, x_4);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_17, x_16, x_1, x_10);
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
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Compiler_LCNF_mkAuxParam(x_19, x_23, x_6, x_7, x_8, x_9, x_20);
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
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; size_t x_57; size_t x_58; lean_object* x_59; size_t x_60; size_t x_61; size_t x_62; lean_object* x_63; uint8_t x_64; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
x_32 = lean_ctor_get(x_5, 0);
lean_inc(x_32);
lean_dec(x_5);
lean_inc(x_25);
x_33 = lean_array_push(x_28, x_25);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
lean_dec(x_14);
lean_inc(x_34);
x_46 = l_Lean_Expr_fvar___override(x_34);
x_47 = lean_array_get_size(x_31);
x_48 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_45);
x_49 = lean_unsigned_to_nat(32u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_shift_right(x_48, x_50);
x_52 = lean_uint64_xor(x_48, x_51);
x_53 = lean_unsigned_to_nat(16u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_uint64_shift_right(x_52, x_54);
x_56 = lean_uint64_xor(x_52, x_55);
x_57 = lean_uint64_to_usize(x_56);
x_58 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_usize_of_nat(x_59);
x_61 = lean_usize_sub(x_58, x_60);
x_62 = lean_usize_land(x_57, x_61);
x_63 = lean_array_uget(x_31, x_62);
x_64 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_45, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_nat_add(x_30, x_59);
lean_dec(x_30);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_45);
lean_ctor_set(x_66, 1, x_46);
lean_ctor_set(x_66, 2, x_63);
x_67 = lean_array_uset(x_31, x_62, x_66);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_nat_shiftl(x_65, x_68);
x_70 = lean_unsigned_to_nat(3u);
x_71 = lean_nat_div(x_69, x_70);
lean_dec(x_69);
x_72 = lean_array_get_size(x_67);
x_73 = lean_nat_dec_le(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_67);
lean_ctor_set(x_16, 1, x_74);
lean_ctor_set(x_16, 0, x_65);
x_35 = x_16;
goto block_44;
}
else
{
lean_ctor_set(x_16, 1, x_67);
lean_ctor_set(x_16, 0, x_65);
x_35 = x_16;
goto block_44;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_31, x_62, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_45, x_46, x_63);
x_78 = lean_array_uset(x_76, x_62, x_77);
lean_ctor_set(x_16, 1, x_78);
x_35 = x_16;
goto block_44;
}
block_44:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_array_push(x_32, x_36);
if (lean_is_scalar(x_27)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_27;
}
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_35);
if (lean_is_scalar(x_21)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_21;
}
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_add(x_4, x_41);
x_4 = x_42;
x_5 = x_39;
x_10 = x_26;
goto _start;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; lean_object* x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; size_t x_106; size_t x_107; lean_object* x_108; size_t x_109; size_t x_110; size_t x_111; lean_object* x_112; uint8_t x_113; 
x_79 = lean_ctor_get(x_16, 0);
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_16);
x_81 = lean_ctor_get(x_5, 0);
lean_inc(x_81);
lean_dec(x_5);
lean_inc(x_25);
x_82 = lean_array_push(x_28, x_25);
x_83 = lean_ctor_get(x_25, 0);
lean_inc(x_83);
lean_dec(x_25);
x_94 = lean_ctor_get(x_14, 0);
lean_inc(x_94);
lean_dec(x_14);
lean_inc(x_83);
x_95 = l_Lean_Expr_fvar___override(x_83);
x_96 = lean_array_get_size(x_80);
x_97 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_94);
x_98 = lean_unsigned_to_nat(32u);
x_99 = lean_uint64_of_nat(x_98);
x_100 = lean_uint64_shift_right(x_97, x_99);
x_101 = lean_uint64_xor(x_97, x_100);
x_102 = lean_unsigned_to_nat(16u);
x_103 = lean_uint64_of_nat(x_102);
x_104 = lean_uint64_shift_right(x_101, x_103);
x_105 = lean_uint64_xor(x_101, x_104);
x_106 = lean_uint64_to_usize(x_105);
x_107 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_usize_of_nat(x_108);
x_110 = lean_usize_sub(x_107, x_109);
x_111 = lean_usize_land(x_106, x_110);
x_112 = lean_array_uget(x_80, x_111);
x_113 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_94, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_114 = lean_nat_add(x_79, x_108);
lean_dec(x_79);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_94);
lean_ctor_set(x_115, 1, x_95);
lean_ctor_set(x_115, 2, x_112);
x_116 = lean_array_uset(x_80, x_111, x_115);
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
x_84 = x_124;
goto block_93;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_114);
lean_ctor_set(x_125, 1, x_116);
x_84 = x_125;
goto block_93;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_box(0);
x_127 = lean_array_uset(x_80, x_111, x_126);
x_128 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_94, x_95, x_112);
x_129 = lean_array_uset(x_127, x_111, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_79);
lean_ctor_set(x_130, 1, x_129);
x_84 = x_130;
goto block_93;
}
block_93:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_array_push(x_81, x_85);
if (lean_is_scalar(x_27)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_27;
}
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_84);
if (lean_is_scalar(x_21)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_21;
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_usize_of_nat(x_89);
x_91 = lean_usize_add(x_4, x_90);
x_4 = x_91;
x_5 = x_88;
x_10 = x_26;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_27, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set(x_13, 2, x_29);
x_16 = x_13;
x_17 = x_30;
goto block_23;
}
else
{
uint8_t x_31; 
lean_free_object(x_13);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
x_37 = lean_ctor_get(x_13, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_37, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_39);
x_16 = x_41;
x_17 = x_40;
goto block_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_44 = x_38;
} else {
 lean_dec_ref(x_38);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_47, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_ctor_set(x_13, 0, x_49);
x_16 = x_13;
x_17 = x_50;
goto block_23;
}
else
{
uint8_t x_51; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_13, 0);
lean_inc(x_55);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_55, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_16 = x_59;
x_17 = x_58;
goto block_23;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
block_23:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_15, x_3, x_16);
x_3 = x_20;
x_4 = x_21;
x_10 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_3, 2);
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
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_17);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_27);
lean_inc(x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_ctor_get(x_3, 5);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
lean_inc(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
lean_inc(x_37);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_37);
lean_inc(x_37);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_37);
x_44 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
lean_ctor_set(x_44, 7, x_42);
lean_ctor_set(x_44, 8, x_43);
lean_inc(x_35);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_45);
lean_inc(x_31);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_6);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_30);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_6);
x_50 = lean_st_ref_get(x_2, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_3, 5);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec(x_51);
x_57 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_56);
lean_dec(x_56);
x_58 = lean_ctor_get(x_3, 2);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_inc(x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_60);
lean_inc(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
lean_inc(x_60);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_60);
lean_inc(x_60);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_60);
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_61);
lean_ctor_set(x_67, 4, x_62);
lean_ctor_set(x_67, 5, x_63);
lean_ctor_set(x_67, 6, x_64);
lean_ctor_set(x_67, 7, x_65);
lean_ctor_set(x_67, 8, x_66);
lean_inc(x_58);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_57);
lean_ctor_set(x_68, 3, x_58);
x_69 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_1);
lean_inc(x_54);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_53)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_53;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_52);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_11 = x_2;
} else {
 lean_dec_ref(x_2);
 x_11 = lean_box(0);
}
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_10, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_9, 0);
lean_inc(x_70);
x_71 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_70, x_69);
lean_dec(x_69);
lean_dec(x_70);
if (x_71 == 0)
{
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
goto block_68;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_9, 3);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 4)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
x_76 = l_Lean_Compiler_LCNF_getBinderName___redArg(x_74, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Name_getPrefix(x_77);
lean_dec(x_77);
x_80 = lean_mk_string_unchecked("_alt", 4, 4);
x_81 = l_Lean_Name_mkStr1(x_80);
x_82 = lean_name_eq(x_79, x_81);
lean_dec(x_81);
lean_dec(x_79);
if (x_82 == 0)
{
lean_free_object(x_72);
lean_dec(x_75);
lean_dec(x_74);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_78;
goto block_68;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_inc(x_74);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_74, x_4, x_5, x_6, x_7, x_78);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
lean_free_object(x_72);
lean_dec(x_75);
lean_dec(x_74);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_85;
goto block_68;
}
else
{
uint8_t x_86; 
lean_dec(x_11);
lean_dec(x_10);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_83, 1);
x_88 = lean_ctor_get(x_83, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_9, x_5, x_87);
lean_dec(x_9);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_91, 1);
x_94 = lean_ctor_get(x_91, 0);
lean_dec(x_94);
x_95 = lean_st_ref_get(x_3, x_93);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_97, x_74);
lean_dec(x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; size_t x_115; lean_object* x_116; size_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_free_object(x_95);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_mk_empty_array_with_capacity(x_100);
x_102 = lean_unsigned_to_nat(8u);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_nat_shiftl(x_102, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_nat_div(x_104, x_105);
lean_dec(x_104);
x_107 = l_Nat_nextPowerOfTwo(x_106);
lean_dec(x_106);
x_108 = lean_box(0);
x_109 = lean_mk_array(x_107, x_108);
lean_ctor_set(x_91, 1, x_109);
lean_ctor_set(x_91, 0, x_100);
x_110 = lean_ctor_get(x_90, 2);
lean_inc(x_110);
lean_dec(x_90);
x_111 = lean_array_get_size(x_75);
x_112 = l_Array_toSubarray___redArg(x_110, x_100, x_111);
lean_inc(x_101);
lean_ctor_set(x_83, 1, x_91);
lean_ctor_set(x_83, 0, x_101);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_101);
lean_ctor_set(x_113, 1, x_83);
x_114 = lean_ctor_get(x_112, 2);
lean_inc(x_114);
x_115 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
x_117 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_118 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_82, x_112, x_115, x_117, x_113, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_112);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_120);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_120, 0);
x_127 = lean_ctor_get(x_120, 1);
lean_dec(x_127);
lean_inc(x_74);
lean_ctor_set(x_72, 1, x_123);
x_128 = lean_mk_string_unchecked("_x", 2, 2);
x_129 = l_Lean_Name_mkStr1(x_128);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_130 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_72, x_129, x_4, x_5, x_6, x_7, x_121);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_1, 0);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
lean_ctor_set(x_84, 0, x_134);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_mk_empty_array_with_capacity(x_135);
x_137 = lean_array_push(x_136, x_84);
lean_inc(x_133);
lean_ctor_set_tag(x_120, 3);
lean_ctor_set(x_120, 1, x_137);
lean_ctor_set(x_120, 0, x_133);
lean_ctor_set(x_119, 0, x_131);
x_138 = lean_mk_string_unchecked("_jp", 3, 3);
x_139 = l_Lean_Name_mkStr1(x_138);
x_140 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_126, x_119, x_139, x_4, x_5, x_6, x_7, x_132);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_st_ref_take(x_3, x_142);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_141);
x_147 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_145, x_74, x_141);
x_148 = lean_st_ref_set(x_3, x_147, x_146);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
lean_dec(x_150);
x_151 = lean_ctor_get(x_141, 0);
lean_inc(x_151);
lean_dec(x_141);
lean_ctor_set_tag(x_143, 3);
lean_ctor_set(x_143, 1, x_75);
lean_ctor_set(x_143, 0, x_151);
lean_ctor_set(x_148, 0, x_143);
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_ctor_get(x_141, 0);
lean_inc(x_153);
lean_dec(x_141);
lean_ctor_set_tag(x_143, 3);
lean_ctor_set(x_143, 1, x_75);
lean_ctor_set(x_143, 0, x_153);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_143, 0);
x_156 = lean_ctor_get(x_143, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_143);
lean_inc(x_141);
x_157 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_155, x_74, x_141);
x_158 = lean_st_ref_set(x_3, x_157, x_156);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_141, 0);
lean_inc(x_161);
lean_dec(x_141);
x_162 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_75);
if (lean_is_scalar(x_160)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_160;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_159);
return x_163;
}
}
else
{
uint8_t x_164; 
lean_dec(x_75);
lean_dec(x_74);
x_164 = !lean_is_exclusive(x_140);
if (x_164 == 0)
{
return x_140;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_140, 0);
x_166 = lean_ctor_get(x_140, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_140);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_free_object(x_120);
lean_dec(x_126);
lean_free_object(x_119);
lean_free_object(x_84);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_168 = !lean_is_exclusive(x_130);
if (x_168 == 0)
{
return x_130;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_130, 0);
x_170 = lean_ctor_get(x_130, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_130);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_120, 0);
lean_inc(x_172);
lean_dec(x_120);
lean_inc(x_74);
lean_ctor_set(x_72, 1, x_123);
x_173 = lean_mk_string_unchecked("_x", 2, 2);
x_174 = l_Lean_Name_mkStr1(x_173);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_175 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_72, x_174, x_4, x_5, x_6, x_7, x_121);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_1, 0);
x_179 = lean_ctor_get(x_176, 0);
lean_inc(x_179);
lean_ctor_set(x_84, 0, x_179);
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_mk_empty_array_with_capacity(x_180);
x_182 = lean_array_push(x_181, x_84);
lean_inc(x_178);
x_183 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_183, 0, x_178);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_119, 1, x_183);
lean_ctor_set(x_119, 0, x_176);
x_184 = lean_mk_string_unchecked("_jp", 3, 3);
x_185 = l_Lean_Name_mkStr1(x_184);
x_186 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_172, x_119, x_185, x_4, x_5, x_6, x_7, x_177);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_st_ref_take(x_3, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
lean_inc(x_187);
x_193 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_190, x_74, x_187);
x_194 = lean_st_ref_set(x_3, x_193, x_191);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_187, 0);
lean_inc(x_197);
lean_dec(x_187);
if (lean_is_scalar(x_192)) {
 x_198 = lean_alloc_ctor(3, 2, 0);
} else {
 x_198 = x_192;
 lean_ctor_set_tag(x_198, 3);
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_75);
if (lean_is_scalar(x_196)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_196;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_195);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_75);
lean_dec(x_74);
x_200 = lean_ctor_get(x_186, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_186, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_202 = x_186;
} else {
 lean_dec_ref(x_186);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_172);
lean_free_object(x_119);
lean_free_object(x_84);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_204 = lean_ctor_get(x_175, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_175, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_206 = x_175;
} else {
 lean_dec_ref(x_175);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_119, 0);
lean_inc(x_208);
lean_dec(x_119);
x_209 = lean_ctor_get(x_120, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_210 = x_120;
} else {
 lean_dec_ref(x_120);
 x_210 = lean_box(0);
}
lean_inc(x_74);
lean_ctor_set(x_72, 1, x_208);
x_211 = lean_mk_string_unchecked("_x", 2, 2);
x_212 = l_Lean_Name_mkStr1(x_211);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_213 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_72, x_212, x_4, x_5, x_6, x_7, x_121);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_1, 0);
x_217 = lean_ctor_get(x_214, 0);
lean_inc(x_217);
lean_ctor_set(x_84, 0, x_217);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_mk_empty_array_with_capacity(x_218);
x_220 = lean_array_push(x_219, x_84);
lean_inc(x_216);
if (lean_is_scalar(x_210)) {
 x_221 = lean_alloc_ctor(3, 2, 0);
} else {
 x_221 = x_210;
 lean_ctor_set_tag(x_221, 3);
}
lean_ctor_set(x_221, 0, x_216);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_214);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_mk_string_unchecked("_jp", 3, 3);
x_224 = l_Lean_Name_mkStr1(x_223);
x_225 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_209, x_222, x_224, x_4, x_5, x_6, x_7, x_215);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_st_ref_take(x_3, x_227);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
lean_inc(x_226);
x_232 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_229, x_74, x_226);
x_233 = lean_st_ref_set(x_3, x_232, x_230);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_226, 0);
lean_inc(x_236);
lean_dec(x_226);
if (lean_is_scalar(x_231)) {
 x_237 = lean_alloc_ctor(3, 2, 0);
} else {
 x_237 = x_231;
 lean_ctor_set_tag(x_237, 3);
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_75);
if (lean_is_scalar(x_235)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_235;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_234);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_75);
lean_dec(x_74);
x_239 = lean_ctor_get(x_225, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_225, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_241 = x_225;
} else {
 lean_dec_ref(x_225);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_210);
lean_dec(x_209);
lean_free_object(x_84);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_243 = lean_ctor_get(x_213, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_213, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_245 = x_213;
} else {
 lean_dec_ref(x_213);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; 
lean_free_object(x_84);
lean_dec(x_90);
lean_free_object(x_83);
lean_free_object(x_72);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_247 = lean_ctor_get(x_99, 0);
lean_inc(x_247);
lean_dec(x_99);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec(x_247);
lean_ctor_set_tag(x_91, 3);
lean_ctor_set(x_91, 1, x_75);
lean_ctor_set(x_91, 0, x_248);
lean_ctor_set(x_95, 0, x_91);
return x_95;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_95, 0);
x_250 = lean_ctor_get(x_95, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_95);
x_251 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_249, x_74);
lean_dec(x_249);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; size_t x_267; lean_object* x_268; size_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_252 = lean_unsigned_to_nat(0u);
x_253 = lean_mk_empty_array_with_capacity(x_252);
x_254 = lean_unsigned_to_nat(8u);
x_255 = lean_unsigned_to_nat(2u);
x_256 = lean_nat_shiftl(x_254, x_255);
x_257 = lean_unsigned_to_nat(3u);
x_258 = lean_nat_div(x_256, x_257);
lean_dec(x_256);
x_259 = l_Nat_nextPowerOfTwo(x_258);
lean_dec(x_258);
x_260 = lean_box(0);
x_261 = lean_mk_array(x_259, x_260);
lean_ctor_set(x_91, 1, x_261);
lean_ctor_set(x_91, 0, x_252);
x_262 = lean_ctor_get(x_90, 2);
lean_inc(x_262);
lean_dec(x_90);
x_263 = lean_array_get_size(x_75);
x_264 = l_Array_toSubarray___redArg(x_262, x_252, x_263);
lean_inc(x_253);
lean_ctor_set(x_83, 1, x_91);
lean_ctor_set(x_83, 0, x_253);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_83);
x_266 = lean_ctor_get(x_264, 2);
lean_inc(x_266);
x_267 = lean_usize_of_nat(x_266);
lean_dec(x_266);
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
x_269 = lean_usize_of_nat(x_268);
lean_dec(x_268);
x_270 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_82, x_264, x_267, x_269, x_265, x_4, x_5, x_6, x_7, x_250);
lean_dec(x_264);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_ctor_get(x_271, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_275 = x_271;
} else {
 lean_dec_ref(x_271);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_272, 0);
lean_inc(x_276);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_277 = x_272;
} else {
 lean_dec_ref(x_272);
 x_277 = lean_box(0);
}
lean_inc(x_74);
lean_ctor_set(x_72, 1, x_274);
x_278 = lean_mk_string_unchecked("_x", 2, 2);
x_279 = l_Lean_Name_mkStr1(x_278);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_280 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_72, x_279, x_4, x_5, x_6, x_7, x_273);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_ctor_get(x_1, 0);
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
lean_ctor_set(x_84, 0, x_284);
x_285 = lean_unsigned_to_nat(1u);
x_286 = lean_mk_empty_array_with_capacity(x_285);
x_287 = lean_array_push(x_286, x_84);
lean_inc(x_283);
if (lean_is_scalar(x_277)) {
 x_288 = lean_alloc_ctor(3, 2, 0);
} else {
 x_288 = x_277;
 lean_ctor_set_tag(x_288, 3);
}
lean_ctor_set(x_288, 0, x_283);
lean_ctor_set(x_288, 1, x_287);
if (lean_is_scalar(x_275)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_275;
}
lean_ctor_set(x_289, 0, x_281);
lean_ctor_set(x_289, 1, x_288);
x_290 = lean_mk_string_unchecked("_jp", 3, 3);
x_291 = l_Lean_Name_mkStr1(x_290);
x_292 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_276, x_289, x_291, x_4, x_5, x_6, x_7, x_282);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_st_ref_take(x_3, x_294);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_298 = x_295;
} else {
 lean_dec_ref(x_295);
 x_298 = lean_box(0);
}
lean_inc(x_293);
x_299 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_296, x_74, x_293);
x_300 = lean_st_ref_set(x_3, x_299, x_297);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_302 = x_300;
} else {
 lean_dec_ref(x_300);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_293, 0);
lean_inc(x_303);
lean_dec(x_293);
if (lean_is_scalar(x_298)) {
 x_304 = lean_alloc_ctor(3, 2, 0);
} else {
 x_304 = x_298;
 lean_ctor_set_tag(x_304, 3);
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_75);
if (lean_is_scalar(x_302)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_302;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_301);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_75);
lean_dec(x_74);
x_306 = lean_ctor_get(x_292, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_292, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_308 = x_292;
} else {
 lean_dec_ref(x_292);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_free_object(x_84);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_310 = lean_ctor_get(x_280, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_280, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_312 = x_280;
} else {
 lean_dec_ref(x_280);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_free_object(x_84);
lean_dec(x_90);
lean_free_object(x_83);
lean_free_object(x_72);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_314 = lean_ctor_get(x_251, 0);
lean_inc(x_314);
lean_dec(x_251);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_dec(x_314);
lean_ctor_set_tag(x_91, 3);
lean_ctor_set(x_91, 1, x_75);
lean_ctor_set(x_91, 0, x_315);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_91);
lean_ctor_set(x_316, 1, x_250);
return x_316;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_317 = lean_ctor_get(x_91, 1);
lean_inc(x_317);
lean_dec(x_91);
x_318 = lean_st_ref_get(x_3, x_317);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_321 = x_318;
} else {
 lean_dec_ref(x_318);
 x_321 = lean_box(0);
}
x_322 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_319, x_74);
lean_dec(x_319);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; size_t x_339; lean_object* x_340; size_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_321);
x_323 = lean_unsigned_to_nat(0u);
x_324 = lean_mk_empty_array_with_capacity(x_323);
x_325 = lean_unsigned_to_nat(8u);
x_326 = lean_unsigned_to_nat(2u);
x_327 = lean_nat_shiftl(x_325, x_326);
x_328 = lean_unsigned_to_nat(3u);
x_329 = lean_nat_div(x_327, x_328);
lean_dec(x_327);
x_330 = l_Nat_nextPowerOfTwo(x_329);
lean_dec(x_329);
x_331 = lean_box(0);
x_332 = lean_mk_array(x_330, x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_323);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_ctor_get(x_90, 2);
lean_inc(x_334);
lean_dec(x_90);
x_335 = lean_array_get_size(x_75);
x_336 = l_Array_toSubarray___redArg(x_334, x_323, x_335);
lean_inc(x_324);
lean_ctor_set(x_83, 1, x_333);
lean_ctor_set(x_83, 0, x_324);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_324);
lean_ctor_set(x_337, 1, x_83);
x_338 = lean_ctor_get(x_336, 2);
lean_inc(x_338);
x_339 = lean_usize_of_nat(x_338);
lean_dec(x_338);
x_340 = lean_ctor_get(x_336, 1);
lean_inc(x_340);
x_341 = lean_usize_of_nat(x_340);
lean_dec(x_340);
x_342 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_82, x_336, x_339, x_341, x_337, x_4, x_5, x_6, x_7, x_320);
lean_dec(x_336);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 1);
lean_inc(x_345);
lean_dec(x_342);
x_346 = lean_ctor_get(x_343, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_347 = x_343;
} else {
 lean_dec_ref(x_343);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_344, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_349 = x_344;
} else {
 lean_dec_ref(x_344);
 x_349 = lean_box(0);
}
lean_inc(x_74);
lean_ctor_set(x_72, 1, x_346);
x_350 = lean_mk_string_unchecked("_x", 2, 2);
x_351 = l_Lean_Name_mkStr1(x_350);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_352 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_72, x_351, x_4, x_5, x_6, x_7, x_345);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_ctor_get(x_1, 0);
x_356 = lean_ctor_get(x_353, 0);
lean_inc(x_356);
lean_ctor_set(x_84, 0, x_356);
x_357 = lean_unsigned_to_nat(1u);
x_358 = lean_mk_empty_array_with_capacity(x_357);
x_359 = lean_array_push(x_358, x_84);
lean_inc(x_355);
if (lean_is_scalar(x_349)) {
 x_360 = lean_alloc_ctor(3, 2, 0);
} else {
 x_360 = x_349;
 lean_ctor_set_tag(x_360, 3);
}
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_359);
if (lean_is_scalar(x_347)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_347;
}
lean_ctor_set(x_361, 0, x_353);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_mk_string_unchecked("_jp", 3, 3);
x_363 = l_Lean_Name_mkStr1(x_362);
x_364 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_348, x_361, x_363, x_4, x_5, x_6, x_7, x_354);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = lean_st_ref_take(x_3, x_366);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
lean_inc(x_365);
x_371 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_368, x_74, x_365);
x_372 = lean_st_ref_set(x_3, x_371, x_369);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_365, 0);
lean_inc(x_375);
lean_dec(x_365);
if (lean_is_scalar(x_370)) {
 x_376 = lean_alloc_ctor(3, 2, 0);
} else {
 x_376 = x_370;
 lean_ctor_set_tag(x_376, 3);
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_75);
if (lean_is_scalar(x_374)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_374;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_373);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_75);
lean_dec(x_74);
x_378 = lean_ctor_get(x_364, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_364, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_380 = x_364;
} else {
 lean_dec_ref(x_364);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_free_object(x_84);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_382 = lean_ctor_get(x_352, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_352, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_384 = x_352;
} else {
 lean_dec_ref(x_352);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_free_object(x_84);
lean_dec(x_90);
lean_free_object(x_83);
lean_free_object(x_72);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_386 = lean_ctor_get(x_322, 0);
lean_inc(x_386);
lean_dec(x_322);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec(x_386);
x_388 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_75);
if (lean_is_scalar(x_321)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_321;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_320);
return x_389;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_390 = lean_ctor_get(x_84, 0);
lean_inc(x_390);
lean_dec(x_84);
x_391 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_9, x_5, x_87);
lean_dec(x_9);
x_392 = lean_ctor_get(x_391, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_393 = x_391;
} else {
 lean_dec_ref(x_391);
 x_393 = lean_box(0);
}
x_394 = lean_st_ref_get(x_3, x_392);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_397 = x_394;
} else {
 lean_dec_ref(x_394);
 x_397 = lean_box(0);
}
x_398 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_395, x_74);
lean_dec(x_395);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; size_t x_415; lean_object* x_416; size_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_397);
x_399 = lean_unsigned_to_nat(0u);
x_400 = lean_mk_empty_array_with_capacity(x_399);
x_401 = lean_unsigned_to_nat(8u);
x_402 = lean_unsigned_to_nat(2u);
x_403 = lean_nat_shiftl(x_401, x_402);
x_404 = lean_unsigned_to_nat(3u);
x_405 = lean_nat_div(x_403, x_404);
lean_dec(x_403);
x_406 = l_Nat_nextPowerOfTwo(x_405);
lean_dec(x_405);
x_407 = lean_box(0);
x_408 = lean_mk_array(x_406, x_407);
if (lean_is_scalar(x_393)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_393;
}
lean_ctor_set(x_409, 0, x_399);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_ctor_get(x_390, 2);
lean_inc(x_410);
lean_dec(x_390);
x_411 = lean_array_get_size(x_75);
x_412 = l_Array_toSubarray___redArg(x_410, x_399, x_411);
lean_inc(x_400);
lean_ctor_set(x_83, 1, x_409);
lean_ctor_set(x_83, 0, x_400);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_400);
lean_ctor_set(x_413, 1, x_83);
x_414 = lean_ctor_get(x_412, 2);
lean_inc(x_414);
x_415 = lean_usize_of_nat(x_414);
lean_dec(x_414);
x_416 = lean_ctor_get(x_412, 1);
lean_inc(x_416);
x_417 = lean_usize_of_nat(x_416);
lean_dec(x_416);
x_418 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_82, x_412, x_415, x_417, x_413, x_4, x_5, x_6, x_7, x_396);
lean_dec(x_412);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_418, 1);
lean_inc(x_421);
lean_dec(x_418);
x_422 = lean_ctor_get(x_419, 0);
lean_inc(x_422);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_423 = x_419;
} else {
 lean_dec_ref(x_419);
 x_423 = lean_box(0);
}
x_424 = lean_ctor_get(x_420, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_425 = x_420;
} else {
 lean_dec_ref(x_420);
 x_425 = lean_box(0);
}
lean_inc(x_74);
lean_ctor_set(x_72, 1, x_422);
x_426 = lean_mk_string_unchecked("_x", 2, 2);
x_427 = l_Lean_Name_mkStr1(x_426);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_428 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_72, x_427, x_4, x_5, x_6, x_7, x_421);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = lean_ctor_get(x_1, 0);
x_432 = lean_ctor_get(x_429, 0);
lean_inc(x_432);
x_433 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_433, 0, x_432);
x_434 = lean_unsigned_to_nat(1u);
x_435 = lean_mk_empty_array_with_capacity(x_434);
x_436 = lean_array_push(x_435, x_433);
lean_inc(x_431);
if (lean_is_scalar(x_425)) {
 x_437 = lean_alloc_ctor(3, 2, 0);
} else {
 x_437 = x_425;
 lean_ctor_set_tag(x_437, 3);
}
lean_ctor_set(x_437, 0, x_431);
lean_ctor_set(x_437, 1, x_436);
if (lean_is_scalar(x_423)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_423;
}
lean_ctor_set(x_438, 0, x_429);
lean_ctor_set(x_438, 1, x_437);
x_439 = lean_mk_string_unchecked("_jp", 3, 3);
x_440 = l_Lean_Name_mkStr1(x_439);
x_441 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_424, x_438, x_440, x_4, x_5, x_6, x_7, x_430);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
lean_dec(x_441);
x_444 = lean_st_ref_take(x_3, x_443);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_447 = x_444;
} else {
 lean_dec_ref(x_444);
 x_447 = lean_box(0);
}
lean_inc(x_442);
x_448 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_445, x_74, x_442);
x_449 = lean_st_ref_set(x_3, x_448, x_446);
x_450 = lean_ctor_get(x_449, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_451 = x_449;
} else {
 lean_dec_ref(x_449);
 x_451 = lean_box(0);
}
x_452 = lean_ctor_get(x_442, 0);
lean_inc(x_452);
lean_dec(x_442);
if (lean_is_scalar(x_447)) {
 x_453 = lean_alloc_ctor(3, 2, 0);
} else {
 x_453 = x_447;
 lean_ctor_set_tag(x_453, 3);
}
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_75);
if (lean_is_scalar(x_451)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_451;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_450);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_75);
lean_dec(x_74);
x_455 = lean_ctor_get(x_441, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_441, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_457 = x_441;
} else {
 lean_dec_ref(x_441);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_455);
lean_ctor_set(x_458, 1, x_456);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_425);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_459 = lean_ctor_get(x_428, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_428, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_461 = x_428;
} else {
 lean_dec_ref(x_428);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_460);
return x_462;
}
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_390);
lean_free_object(x_83);
lean_free_object(x_72);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_463 = lean_ctor_get(x_398, 0);
lean_inc(x_463);
lean_dec(x_398);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
lean_dec(x_463);
if (lean_is_scalar(x_393)) {
 x_465 = lean_alloc_ctor(3, 2, 0);
} else {
 x_465 = x_393;
 lean_ctor_set_tag(x_465, 3);
}
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_75);
if (lean_is_scalar(x_397)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_397;
}
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_396);
return x_466;
}
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_467 = lean_ctor_get(x_83, 1);
lean_inc(x_467);
lean_dec(x_83);
x_468 = lean_ctor_get(x_84, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_469 = x_84;
} else {
 lean_dec_ref(x_84);
 x_469 = lean_box(0);
}
x_470 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_9, x_5, x_467);
lean_dec(x_9);
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
x_473 = lean_st_ref_get(x_3, x_471);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_476 = x_473;
} else {
 lean_dec_ref(x_473);
 x_476 = lean_box(0);
}
x_477 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_474, x_74);
lean_dec(x_474);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; size_t x_495; lean_object* x_496; size_t x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_476);
x_478 = lean_unsigned_to_nat(0u);
x_479 = lean_mk_empty_array_with_capacity(x_478);
x_480 = lean_unsigned_to_nat(8u);
x_481 = lean_unsigned_to_nat(2u);
x_482 = lean_nat_shiftl(x_480, x_481);
x_483 = lean_unsigned_to_nat(3u);
x_484 = lean_nat_div(x_482, x_483);
lean_dec(x_482);
x_485 = l_Nat_nextPowerOfTwo(x_484);
lean_dec(x_484);
x_486 = lean_box(0);
x_487 = lean_mk_array(x_485, x_486);
if (lean_is_scalar(x_472)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_472;
}
lean_ctor_set(x_488, 0, x_478);
lean_ctor_set(x_488, 1, x_487);
x_489 = lean_ctor_get(x_468, 2);
lean_inc(x_489);
lean_dec(x_468);
x_490 = lean_array_get_size(x_75);
x_491 = l_Array_toSubarray___redArg(x_489, x_478, x_490);
lean_inc(x_479);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_479);
lean_ctor_set(x_492, 1, x_488);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_479);
lean_ctor_set(x_493, 1, x_492);
x_494 = lean_ctor_get(x_491, 2);
lean_inc(x_494);
x_495 = lean_usize_of_nat(x_494);
lean_dec(x_494);
x_496 = lean_ctor_get(x_491, 1);
lean_inc(x_496);
x_497 = lean_usize_of_nat(x_496);
lean_dec(x_496);
x_498 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_82, x_491, x_495, x_497, x_493, x_4, x_5, x_6, x_7, x_475);
lean_dec(x_491);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_499, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_498, 1);
lean_inc(x_501);
lean_dec(x_498);
x_502 = lean_ctor_get(x_499, 0);
lean_inc(x_502);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_503 = x_499;
} else {
 lean_dec_ref(x_499);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_500, 0);
lean_inc(x_504);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_505 = x_500;
} else {
 lean_dec_ref(x_500);
 x_505 = lean_box(0);
}
lean_inc(x_74);
lean_ctor_set(x_72, 1, x_502);
x_506 = lean_mk_string_unchecked("_x", 2, 2);
x_507 = l_Lean_Name_mkStr1(x_506);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_508 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_72, x_507, x_4, x_5, x_6, x_7, x_501);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_ctor_get(x_1, 0);
x_512 = lean_ctor_get(x_509, 0);
lean_inc(x_512);
if (lean_is_scalar(x_469)) {
 x_513 = lean_alloc_ctor(1, 1, 0);
} else {
 x_513 = x_469;
}
lean_ctor_set(x_513, 0, x_512);
x_514 = lean_unsigned_to_nat(1u);
x_515 = lean_mk_empty_array_with_capacity(x_514);
x_516 = lean_array_push(x_515, x_513);
lean_inc(x_511);
if (lean_is_scalar(x_505)) {
 x_517 = lean_alloc_ctor(3, 2, 0);
} else {
 x_517 = x_505;
 lean_ctor_set_tag(x_517, 3);
}
lean_ctor_set(x_517, 0, x_511);
lean_ctor_set(x_517, 1, x_516);
if (lean_is_scalar(x_503)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_503;
}
lean_ctor_set(x_518, 0, x_509);
lean_ctor_set(x_518, 1, x_517);
x_519 = lean_mk_string_unchecked("_jp", 3, 3);
x_520 = l_Lean_Name_mkStr1(x_519);
x_521 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_504, x_518, x_520, x_4, x_5, x_6, x_7, x_510);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = lean_st_ref_take(x_3, x_523);
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_527 = x_524;
} else {
 lean_dec_ref(x_524);
 x_527 = lean_box(0);
}
lean_inc(x_522);
x_528 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_525, x_74, x_522);
x_529 = lean_st_ref_set(x_3, x_528, x_526);
x_530 = lean_ctor_get(x_529, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_531 = x_529;
} else {
 lean_dec_ref(x_529);
 x_531 = lean_box(0);
}
x_532 = lean_ctor_get(x_522, 0);
lean_inc(x_532);
lean_dec(x_522);
if (lean_is_scalar(x_527)) {
 x_533 = lean_alloc_ctor(3, 2, 0);
} else {
 x_533 = x_527;
 lean_ctor_set_tag(x_533, 3);
}
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_75);
if (lean_is_scalar(x_531)) {
 x_534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_534 = x_531;
}
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_530);
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_75);
lean_dec(x_74);
x_535 = lean_ctor_get(x_521, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_521, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_537 = x_521;
} else {
 lean_dec_ref(x_521);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_535);
lean_ctor_set(x_538, 1, x_536);
return x_538;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_469);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_539 = lean_ctor_get(x_508, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_508, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_541 = x_508;
} else {
 lean_dec_ref(x_508);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 2, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_469);
lean_dec(x_468);
lean_free_object(x_72);
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_543 = lean_ctor_get(x_477, 0);
lean_inc(x_543);
lean_dec(x_477);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
lean_dec(x_543);
if (lean_is_scalar(x_472)) {
 x_545 = lean_alloc_ctor(3, 2, 0);
} else {
 x_545 = x_472;
 lean_ctor_set_tag(x_545, 3);
}
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_75);
if (lean_is_scalar(x_476)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_476;
}
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_475);
return x_546;
}
}
}
}
}
else
{
uint8_t x_547; 
lean_free_object(x_72);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_547 = !lean_is_exclusive(x_76);
if (x_547 == 0)
{
return x_76;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_76, 0);
x_549 = lean_ctor_get(x_76, 1);
lean_inc(x_549);
lean_inc(x_548);
lean_dec(x_76);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
return x_550;
}
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_72, 0);
x_552 = lean_ctor_get(x_72, 1);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_72);
lean_inc(x_551);
x_553 = l_Lean_Compiler_LCNF_getBinderName___redArg(x_551, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = l_Lean_Name_getPrefix(x_554);
lean_dec(x_554);
x_557 = lean_mk_string_unchecked("_alt", 4, 4);
x_558 = l_Lean_Name_mkStr1(x_557);
x_559 = lean_name_eq(x_556, x_558);
lean_dec(x_558);
lean_dec(x_556);
if (x_559 == 0)
{
lean_dec(x_552);
lean_dec(x_551);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_555;
goto block_68;
}
else
{
lean_object* x_560; lean_object* x_561; 
lean_inc(x_551);
x_560 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_551, x_4, x_5, x_6, x_7, x_555);
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; 
lean_dec(x_552);
lean_dec(x_551);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_562;
goto block_68;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec(x_11);
lean_dec(x_10);
x_563 = lean_ctor_get(x_560, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_564 = x_560;
} else {
 lean_dec_ref(x_560);
 x_564 = lean_box(0);
}
x_565 = lean_ctor_get(x_561, 0);
lean_inc(x_565);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 x_566 = x_561;
} else {
 lean_dec_ref(x_561);
 x_566 = lean_box(0);
}
x_567 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_9, x_5, x_563);
lean_dec(x_9);
x_568 = lean_ctor_get(x_567, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_569 = x_567;
} else {
 lean_dec_ref(x_567);
 x_569 = lean_box(0);
}
x_570 = lean_st_ref_get(x_3, x_568);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_573 = x_570;
} else {
 lean_dec_ref(x_570);
 x_573 = lean_box(0);
}
x_574 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_571, x_551);
lean_dec(x_571);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; size_t x_592; lean_object* x_593; size_t x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_573);
x_575 = lean_unsigned_to_nat(0u);
x_576 = lean_mk_empty_array_with_capacity(x_575);
x_577 = lean_unsigned_to_nat(8u);
x_578 = lean_unsigned_to_nat(2u);
x_579 = lean_nat_shiftl(x_577, x_578);
x_580 = lean_unsigned_to_nat(3u);
x_581 = lean_nat_div(x_579, x_580);
lean_dec(x_579);
x_582 = l_Nat_nextPowerOfTwo(x_581);
lean_dec(x_581);
x_583 = lean_box(0);
x_584 = lean_mk_array(x_582, x_583);
if (lean_is_scalar(x_569)) {
 x_585 = lean_alloc_ctor(0, 2, 0);
} else {
 x_585 = x_569;
}
lean_ctor_set(x_585, 0, x_575);
lean_ctor_set(x_585, 1, x_584);
x_586 = lean_ctor_get(x_565, 2);
lean_inc(x_586);
lean_dec(x_565);
x_587 = lean_array_get_size(x_552);
x_588 = l_Array_toSubarray___redArg(x_586, x_575, x_587);
lean_inc(x_576);
if (lean_is_scalar(x_564)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_564;
}
lean_ctor_set(x_589, 0, x_576);
lean_ctor_set(x_589, 1, x_585);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_576);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_ctor_get(x_588, 2);
lean_inc(x_591);
x_592 = lean_usize_of_nat(x_591);
lean_dec(x_591);
x_593 = lean_ctor_get(x_588, 1);
lean_inc(x_593);
x_594 = lean_usize_of_nat(x_593);
lean_dec(x_593);
x_595 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_559, x_588, x_592, x_594, x_590, x_4, x_5, x_6, x_7, x_572);
lean_dec(x_588);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
x_598 = lean_ctor_get(x_595, 1);
lean_inc(x_598);
lean_dec(x_595);
x_599 = lean_ctor_get(x_596, 0);
lean_inc(x_599);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_600 = x_596;
} else {
 lean_dec_ref(x_596);
 x_600 = lean_box(0);
}
x_601 = lean_ctor_get(x_597, 0);
lean_inc(x_601);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_602 = x_597;
} else {
 lean_dec_ref(x_597);
 x_602 = lean_box(0);
}
lean_inc(x_551);
x_603 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_603, 0, x_551);
lean_ctor_set(x_603, 1, x_599);
x_604 = lean_mk_string_unchecked("_x", 2, 2);
x_605 = l_Lean_Name_mkStr1(x_604);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_606 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_603, x_605, x_4, x_5, x_6, x_7, x_598);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = lean_ctor_get(x_1, 0);
x_610 = lean_ctor_get(x_607, 0);
lean_inc(x_610);
if (lean_is_scalar(x_566)) {
 x_611 = lean_alloc_ctor(1, 1, 0);
} else {
 x_611 = x_566;
}
lean_ctor_set(x_611, 0, x_610);
x_612 = lean_unsigned_to_nat(1u);
x_613 = lean_mk_empty_array_with_capacity(x_612);
x_614 = lean_array_push(x_613, x_611);
lean_inc(x_609);
if (lean_is_scalar(x_602)) {
 x_615 = lean_alloc_ctor(3, 2, 0);
} else {
 x_615 = x_602;
 lean_ctor_set_tag(x_615, 3);
}
lean_ctor_set(x_615, 0, x_609);
lean_ctor_set(x_615, 1, x_614);
if (lean_is_scalar(x_600)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_600;
}
lean_ctor_set(x_616, 0, x_607);
lean_ctor_set(x_616, 1, x_615);
x_617 = lean_mk_string_unchecked("_jp", 3, 3);
x_618 = l_Lean_Name_mkStr1(x_617);
x_619 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_601, x_616, x_618, x_4, x_5, x_6, x_7, x_608);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
x_622 = lean_st_ref_take(x_3, x_621);
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_625 = x_622;
} else {
 lean_dec_ref(x_622);
 x_625 = lean_box(0);
}
lean_inc(x_620);
x_626 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_623, x_551, x_620);
x_627 = lean_st_ref_set(x_3, x_626, x_624);
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_629 = x_627;
} else {
 lean_dec_ref(x_627);
 x_629 = lean_box(0);
}
x_630 = lean_ctor_get(x_620, 0);
lean_inc(x_630);
lean_dec(x_620);
if (lean_is_scalar(x_625)) {
 x_631 = lean_alloc_ctor(3, 2, 0);
} else {
 x_631 = x_625;
 lean_ctor_set_tag(x_631, 3);
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_552);
if (lean_is_scalar(x_629)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_629;
}
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_628);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_552);
lean_dec(x_551);
x_633 = lean_ctor_get(x_619, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_619, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_635 = x_619;
} else {
 lean_dec_ref(x_619);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
return x_636;
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_566);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_637 = lean_ctor_get(x_606, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_606, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_639 = x_606;
} else {
 lean_dec_ref(x_606);
 x_639 = lean_box(0);
}
if (lean_is_scalar(x_639)) {
 x_640 = lean_alloc_ctor(1, 2, 0);
} else {
 x_640 = x_639;
}
lean_ctor_set(x_640, 0, x_637);
lean_ctor_set(x_640, 1, x_638);
return x_640;
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_551);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_641 = lean_ctor_get(x_574, 0);
lean_inc(x_641);
lean_dec(x_574);
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
lean_dec(x_641);
if (lean_is_scalar(x_569)) {
 x_643 = lean_alloc_ctor(3, 2, 0);
} else {
 x_643 = x_569;
 lean_ctor_set_tag(x_643, 3);
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_552);
if (lean_is_scalar(x_573)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_573;
}
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_572);
return x_644;
}
}
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_645 = lean_ctor_get(x_553, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_553, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 x_647 = x_553;
} else {
 lean_dec_ref(x_553);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(1, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_645);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
}
}
else
{
lean_dec(x_72);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
goto block_68;
}
}
}
else
{
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
goto block_68;
}
block_68:
{
lean_object* x_18; 
x_18 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_10, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_12, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
x_26 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_23, x_25);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_25);
if (lean_is_scalar(x_11)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_11;
}
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_free_object(x_21);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_take(x_12, x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = l_Lean_RBNode_erase___at___Lean_LocalContext_erase_spec__1___redArg(x_25, x_31);
lean_dec(x_25);
x_34 = lean_st_ref_set(x_12, x_33, x_32);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
if (lean_is_scalar(x_11)) {
 x_37 = lean_alloc_ctor(2, 2, 0);
} else {
 x_37 = x_11;
 lean_ctor_set_tag(x_37, 2);
}
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_19);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_34, 0, x_29);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
if (lean_is_scalar(x_11)) {
 x_39 = lean_alloc_ctor(2, 2, 0);
} else {
 x_39 = x_11;
 lean_ctor_set_tag(x_39, 2);
}
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_19);
lean_ctor_set(x_29, 1, x_39);
lean_ctor_set(x_29, 0, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_29, 0);
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_29);
x_43 = l_Lean_RBNode_erase___at___Lean_LocalContext_erase_spec__1___redArg(x_25, x_41);
lean_dec(x_25);
x_44 = lean_st_ref_set(x_12, x_43, x_42);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_11)) {
 x_47 = lean_alloc_ctor(2, 2, 0);
} else {
 x_47 = x_11;
 lean_ctor_set_tag(x_47, 2);
}
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_19);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_ctor_get(x_9, 0);
lean_inc(x_52);
x_53 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_50, x_52);
lean_dec(x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
if (lean_is_scalar(x_11)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_11;
}
lean_ctor_set(x_54, 0, x_9);
lean_ctor_set(x_54, 1, x_19);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_st_ref_take(x_12, x_51);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = l_Lean_RBNode_erase___at___Lean_LocalContext_erase_spec__1___redArg(x_52, x_58);
lean_dec(x_52);
x_62 = lean_st_ref_set(x_12, x_61, x_59);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_11)) {
 x_65 = lean_alloc_ctor(2, 2, 0);
} else {
 x_65 = x_11;
 lean_ctor_set_tag(x_65, 2);
}
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_19);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_9);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
return x_18;
}
}
}
case 1:
{
uint8_t x_649; 
x_649 = !lean_is_exclusive(x_2);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_2, 0);
x_651 = lean_ctor_get(x_2, 1);
x_652 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_651, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_652) == 0)
{
uint8_t x_653; 
x_653 = !lean_is_exclusive(x_652);
if (x_653 == 0)
{
lean_object* x_654; 
x_654 = lean_ctor_get(x_652, 0);
lean_ctor_set(x_2, 1, x_654);
lean_ctor_set(x_652, 0, x_2);
return x_652;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_652, 0);
x_656 = lean_ctor_get(x_652, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_652);
lean_ctor_set(x_2, 1, x_655);
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_2);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_650);
return x_652;
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_2, 0);
x_659 = lean_ctor_get(x_2, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_2);
x_660 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_659, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_663 = x_660;
} else {
 lean_dec_ref(x_660);
 x_663 = lean_box(0);
}
x_664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_664, 0, x_658);
lean_ctor_set(x_664, 1, x_661);
if (lean_is_scalar(x_663)) {
 x_665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_665 = x_663;
}
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_662);
return x_665;
}
else
{
lean_dec(x_658);
return x_660;
}
}
}
case 2:
{
uint8_t x_666; 
x_666 = !lean_is_exclusive(x_2);
if (x_666 == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_667 = lean_ctor_get(x_2, 0);
x_668 = lean_ctor_get(x_2, 1);
x_669 = lean_ctor_get(x_667, 4);
lean_inc(x_669);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_670 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_669, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
lean_dec(x_670);
x_673 = lean_ctor_get(x_667, 2);
lean_inc(x_673);
lean_inc(x_671);
lean_inc(x_673);
x_674 = l_Lean_Compiler_LCNF_Code_inferParamType(x_673, x_671, x_4, x_5, x_6, x_7, x_672);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_677 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_667, x_675, x_673, x_671, x_5, x_676);
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_677, 1);
lean_inc(x_679);
lean_dec(x_677);
x_680 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_668, x_3, x_4, x_5, x_6, x_7, x_679);
if (lean_obj_tag(x_680) == 0)
{
uint8_t x_681; 
x_681 = !lean_is_exclusive(x_680);
if (x_681 == 0)
{
lean_object* x_682; 
x_682 = lean_ctor_get(x_680, 0);
lean_ctor_set(x_2, 1, x_682);
lean_ctor_set(x_2, 0, x_678);
lean_ctor_set(x_680, 0, x_2);
return x_680;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_680, 0);
x_684 = lean_ctor_get(x_680, 1);
lean_inc(x_684);
lean_inc(x_683);
lean_dec(x_680);
lean_ctor_set(x_2, 1, x_683);
lean_ctor_set(x_2, 0, x_678);
x_685 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_685, 0, x_2);
lean_ctor_set(x_685, 1, x_684);
return x_685;
}
}
else
{
lean_dec(x_678);
lean_free_object(x_2);
return x_680;
}
}
else
{
uint8_t x_686; 
lean_dec(x_673);
lean_dec(x_671);
lean_free_object(x_2);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_686 = !lean_is_exclusive(x_674);
if (x_686 == 0)
{
return x_674;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_674, 0);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
lean_inc(x_687);
lean_dec(x_674);
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
return x_689;
}
}
}
else
{
lean_free_object(x_2);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_670;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_690 = lean_ctor_get(x_2, 0);
x_691 = lean_ctor_get(x_2, 1);
lean_inc(x_691);
lean_inc(x_690);
lean_dec(x_2);
x_692 = lean_ctor_get(x_690, 4);
lean_inc(x_692);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_693 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_692, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_696 = lean_ctor_get(x_690, 2);
lean_inc(x_696);
lean_inc(x_694);
lean_inc(x_696);
x_697 = l_Lean_Compiler_LCNF_Code_inferParamType(x_696, x_694, x_4, x_5, x_6, x_7, x_695);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
lean_dec(x_697);
x_700 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_690, x_698, x_696, x_694, x_5, x_699);
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
x_703 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_691, x_3, x_4, x_5, x_6, x_7, x_702);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_706 = x_703;
} else {
 lean_dec_ref(x_703);
 x_706 = lean_box(0);
}
x_707 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_707, 0, x_701);
lean_ctor_set(x_707, 1, x_704);
if (lean_is_scalar(x_706)) {
 x_708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_708 = x_706;
}
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_705);
return x_708;
}
else
{
lean_dec(x_701);
return x_703;
}
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_696);
lean_dec(x_694);
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_709 = lean_ctor_get(x_697, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_697, 1);
lean_inc(x_710);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_711 = x_697;
} else {
 lean_dec_ref(x_697);
 x_711 = lean_box(0);
}
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_709);
lean_ctor_set(x_712, 1, x_710);
return x_712;
}
}
else
{
lean_dec(x_691);
lean_dec(x_690);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_693;
}
}
}
case 4:
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; size_t x_716; lean_object* x_717; size_t x_718; lean_object* x_719; 
x_713 = lean_ctor_get(x_2, 0);
lean_inc(x_713);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_714 = x_2;
} else {
 lean_dec_ref(x_2);
 x_714 = lean_box(0);
}
x_715 = lean_ctor_get(x_713, 3);
lean_inc(x_715);
x_716 = lean_array_size(x_715);
x_717 = lean_unsigned_to_nat(0u);
x_718 = lean_usize_of_nat(x_717);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_719 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(x_1, x_716, x_718, x_715, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_746; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_746 = l_Array_isEmpty___redArg(x_720);
if (x_746 == 0)
{
x_722 = x_4;
x_723 = x_5;
x_724 = x_6;
x_725 = x_7;
x_726 = x_721;
goto block_745;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; 
lean_dec(x_720);
lean_dec(x_714);
lean_dec(x_713);
lean_dec(x_4);
x_747 = lean_mk_string_unchecked("`Code.bind` failed, empty `cases` found", 39, 39);
x_748 = l_Lean_stringToMessageData(x_747);
lean_dec(x_747);
x_749 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_748, x_5, x_6, x_7, x_721);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_750 = !lean_is_exclusive(x_749);
if (x_750 == 0)
{
return x_749;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_749, 0);
x_752 = lean_ctor_get(x_749, 1);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_749);
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_752);
return x_753;
}
}
block_745:
{
lean_object* x_727; 
lean_inc(x_720);
x_727 = l_Lean_Compiler_LCNF_mkCasesResultType(x_720, x_722, x_723, x_724, x_725, x_726);
lean_dec(x_725);
lean_dec(x_724);
lean_dec(x_723);
lean_dec(x_722);
if (lean_obj_tag(x_727) == 0)
{
uint8_t x_728; 
x_728 = !lean_is_exclusive(x_727);
if (x_728 == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_729 = lean_ctor_get(x_727, 0);
x_730 = lean_ctor_get(x_713, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_713, 2);
lean_inc(x_731);
lean_dec(x_713);
x_732 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_729);
lean_ctor_set(x_732, 2, x_731);
lean_ctor_set(x_732, 3, x_720);
if (lean_is_scalar(x_714)) {
 x_733 = lean_alloc_ctor(4, 1, 0);
} else {
 x_733 = x_714;
}
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_727, 0, x_733);
return x_727;
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_734 = lean_ctor_get(x_727, 0);
x_735 = lean_ctor_get(x_727, 1);
lean_inc(x_735);
lean_inc(x_734);
lean_dec(x_727);
x_736 = lean_ctor_get(x_713, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_713, 2);
lean_inc(x_737);
lean_dec(x_713);
x_738 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_738, 0, x_736);
lean_ctor_set(x_738, 1, x_734);
lean_ctor_set(x_738, 2, x_737);
lean_ctor_set(x_738, 3, x_720);
if (lean_is_scalar(x_714)) {
 x_739 = lean_alloc_ctor(4, 1, 0);
} else {
 x_739 = x_714;
}
lean_ctor_set(x_739, 0, x_738);
x_740 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_735);
return x_740;
}
}
else
{
uint8_t x_741; 
lean_dec(x_720);
lean_dec(x_714);
lean_dec(x_713);
x_741 = !lean_is_exclusive(x_727);
if (x_741 == 0)
{
return x_727;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_727, 0);
x_743 = lean_ctor_get(x_727, 1);
lean_inc(x_743);
lean_inc(x_742);
lean_dec(x_727);
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set(x_744, 1, x_743);
return x_744;
}
}
}
}
else
{
uint8_t x_754; 
lean_dec(x_714);
lean_dec(x_713);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_754 = !lean_is_exclusive(x_719);
if (x_754 == 0)
{
return x_719;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_755 = lean_ctor_get(x_719, 0);
x_756 = lean_ctor_get(x_719, 1);
lean_inc(x_756);
lean_inc(x_755);
lean_dec(x_719);
x_757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_756);
return x_757;
}
}
}
case 5:
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_758 = lean_ctor_get(x_2, 0);
lean_inc(x_758);
lean_dec(x_2);
x_759 = lean_ctor_get(x_1, 0);
x_760 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_760, 0, x_758);
x_761 = lean_unsigned_to_nat(1u);
x_762 = lean_mk_empty_array_with_capacity(x_761);
x_763 = lean_array_push(x_762, x_760);
lean_inc(x_759);
x_764 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_764, 0, x_759);
lean_ctor_set(x_764, 1, x_763);
x_765 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_8);
return x_765;
}
default: 
{
lean_object* x_766; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_766 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_766, 0, x_2);
lean_ctor_set(x_766, 1, x_8);
return x_766;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_13, 2);
lean_inc(x_31);
x_16 = x_31;
goto block_30;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
x_16 = x_32;
goto block_30;
}
block_30:
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_15, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_array_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(x_1, x_9, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_1, x_3);
lean_inc(x_4);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_12, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_10, x_15);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_14);
x_20 = l_Lean_Compiler_LCNF_mkCasesResultType(x_14, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_14);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_26, x_18);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_27);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_14);
x_33 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_33, x_18);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_34);
lean_ctor_set(x_16, 0, x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_16);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
lean_inc(x_14);
x_42 = l_Lean_Compiler_LCNF_mkCasesResultType(x_14, x_3, x_4, x_5, x_6, x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
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
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
lean_dec(x_2);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_14);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_49, x_40);
lean_dec(x_40);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_45)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_45;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_55 = x_42;
} else {
 lean_dec_ref(x_42);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_13);
if (x_57 == 0)
{
return x_13;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_13, 0);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_13);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_28; 
x_28 = lean_usize_dec_eq(x_2, x_3);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_4);
x_29 = lean_array_uget(x_1, x_2);
switch (lean_obj_tag(x_29)) {
case 2:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_30, x_6, x_9);
lean_dec(x_30);
x_10 = x_31;
goto block_17;
}
case 3:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_33, x_6, x_9);
lean_dec(x_33);
x_10 = x_34;
goto block_17;
}
case 4:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Lean_Compiler_LCNF_eraseParam(x_35, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_35);
x_10 = x_36;
goto block_17;
}
default: 
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_18 = x_37;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
goto block_27;
}
}
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
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
x_9 = x_12;
goto _start;
}
block_27:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Compiler_LCNF_eraseFunDecl(x_18, x_25, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_18);
x_10 = x_26;
goto block_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_2, x_24);
x_26 = lean_array_get(x_23, x_1, x_25);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_2 = x_25;
x_3 = x_28;
goto _start;
}
case 1:
{
lean_object* x_30; 
lean_dec(x_25);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_9 = x_30;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_19;
}
case 2:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
x_2 = x_25;
x_3 = x_32;
goto _start;
}
case 3:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_2);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_37, x_36);
lean_dec(x_36);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
x_2 = x_25;
goto _start;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_3, 0);
lean_dec(x_41);
x_42 = l_Lean_Compiler_LCNF_eraseParam(x_34, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_34);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_ctor_set_tag(x_3, 4);
lean_ctor_set(x_3, 0, x_35);
x_2 = x_25;
x_8 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_45 = l_Lean_Compiler_LCNF_eraseParam(x_34, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_34);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_47, 0, x_35);
x_2 = x_25;
x_3 = x_47;
x_8 = x_46;
goto _start;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_26, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_26, 1);
lean_inc(x_50);
lean_dec(x_26);
x_51 = lean_ctor_get(x_49, 2);
lean_inc(x_51);
lean_inc(x_51);
x_52 = l_Lean_Expr_headBeta(x_51);
x_53 = l_Lean_Expr_isForall(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_2);
x_54 = lean_mk_string_unchecked("_jp", 3, 3);
x_55 = l_Lean_Name_mkStr1(x_54);
x_56 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_49, x_3, x_55, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_59 = l_Lean_Compiler_LCNF_ToLCNF_bindCases(x_57, x_50, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_2 = x_25;
x_3 = x_60;
x_8 = x_61;
goto _start;
}
else
{
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_59;
}
}
else
{
uint8_t x_63; 
lean_dec(x_50);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_56);
if (x_63 == 0)
{
return x_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_56, 0);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_25);
x_67 = l_Lean_Compiler_LCNF_eraseParam(x_49, x_4, x_5, x_6, x_7, x_8);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_5, x_68);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_ctor_get(x_49, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_49, 1);
lean_inc(x_74);
lean_dec(x_49);
x_75 = lean_mk_empty_array_with_capacity(x_20);
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_50);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_51);
lean_ctor_set(x_77, 4, x_76);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_inc(x_77);
x_79 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_78, x_77);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_dec(x_71);
lean_ctor_set(x_69, 1, x_80);
lean_ctor_set(x_69, 0, x_79);
x_81 = lean_st_ref_set(x_5, x_69, x_72);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_83 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_77, x_4, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_9 = x_84;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_85;
goto block_19;
}
else
{
uint8_t x_86; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_83);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_90 = lean_ctor_get(x_69, 0);
x_91 = lean_ctor_get(x_69, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_69);
x_92 = lean_ctor_get(x_49, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_49, 1);
lean_inc(x_93);
lean_dec(x_49);
x_94 = lean_mk_empty_array_with_capacity(x_20);
x_95 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_95, 0, x_50);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_93);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_51);
lean_ctor_set(x_96, 4, x_95);
x_97 = lean_ctor_get(x_90, 0);
lean_inc(x_97);
lean_inc(x_96);
x_98 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_97, x_96);
x_99 = lean_ctor_get(x_90, 1);
lean_inc(x_99);
lean_dec(x_90);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_st_ref_set(x_5, x_100, x_91);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_103 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_96, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_9 = x_104;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_105;
goto block_19;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_108 = x_103;
} else {
 lean_dec_ref(x_103);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
}
default: 
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_25);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_110 = x_26;
} else {
 lean_dec_ref(x_26);
 x_110 = lean_box(0);
}
lean_inc(x_3);
x_111 = l_Lean_Compiler_LCNF_Code_inferType(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_119 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_3, x_5, x_113);
lean_dec(x_3);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_Array_toSubarray___redArg(x_1, x_20, x_2);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 2);
lean_inc(x_123);
x_124 = lean_nat_dec_lt(x_122, x_123);
if (x_124 == 0)
{
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_115 = x_120;
goto block_118;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
lean_dec(x_121);
x_126 = lean_array_get_size(x_125);
x_127 = lean_nat_dec_le(x_123, x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_115 = x_120;
goto block_118;
}
else
{
lean_object* x_128; size_t x_129; size_t x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_box(0);
x_129 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_130 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_131 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(x_125, x_129, x_130, x_128, x_4, x_5, x_6, x_7, x_120);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_125);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_115 = x_132;
goto block_118;
}
}
block_118:
{
lean_object* x_116; lean_object* x_117; 
if (lean_is_scalar(x_110)) {
 x_116 = lean_alloc_ctor(6, 1, 0);
} else {
 x_116 = x_110;
 lean_ctor_set_tag(x_116, 6);
}
lean_ctor_set(x_116, 0, x_112);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_114;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
uint8_t x_133; 
lean_dec(x_110);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_111);
if (x_133 == 0)
{
return x_111;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_111, 0);
x_135 = lean_ctor_get(x_111, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_111);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_16;
x_3 = x_17;
x_4 = x_10;
x_5 = x_11;
x_6 = x_12;
x_7 = x_13;
x_8 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
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
lean_inc(x_12);
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
lean_inc(x_11);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_11);
lean_inc(x_11);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_11);
lean_inc(x_11);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_11);
lean_inc(x_11);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_11);
lean_inc(x_22);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_unsigned_to_nat(5u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_to_nat(x_26);
x_28 = lean_nat_pow(x_24, x_27);
lean_dec(x_27);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_mk_empty_array_with_capacity(x_30);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_10);
lean_ctor_set(x_33, 3, x_10);
lean_ctor_set_usize(x_33, 4, x_26);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_11);
lean_inc_n(x_12, 2);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_12);
lean_ctor_set(x_35, 1, x_12);
lean_ctor_set(x_35, 2, x_12);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_9);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_35);
x_37 = lean_st_mk_ref(x_36, x_8);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(1);
x_41 = lean_box(1);
x_42 = lean_box(0);
x_43 = lean_box(2);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 0, 18);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, 0, x_46);
x_47 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, 1, x_47);
x_48 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, 2, x_48);
x_49 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, 3, x_49);
x_50 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, 4, x_50);
x_51 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 5, x_51);
x_52 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 6, x_52);
x_53 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, 7, x_53);
x_54 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 8, x_54);
x_55 = lean_unbox(x_41);
lean_ctor_set_uint8(x_45, 9, x_55);
x_56 = lean_unbox(x_42);
lean_ctor_set_uint8(x_45, 10, x_56);
x_57 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 11, x_57);
x_58 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 12, x_58);
x_59 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 13, x_59);
x_60 = lean_unbox(x_43);
lean_ctor_set_uint8(x_45, 14, x_60);
x_61 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 15, x_61);
x_62 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 16, x_62);
x_63 = lean_unbox(x_40);
lean_ctor_set_uint8(x_45, 17, x_63);
x_64 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_45);
x_65 = lean_ctor_get(x_7, 0);
lean_inc(x_65);
lean_dec(x_7);
x_66 = lean_mk_empty_array_with_capacity(x_10);
x_67 = lean_box(0);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_69, 0, x_45);
lean_ctor_set(x_69, 1, x_9);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_10);
lean_ctor_set(x_69, 6, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*7, x_64);
x_70 = lean_unbox(x_44);
lean_ctor_set_uint8(x_69, sizeof(void*)*7 + 8, x_70);
x_71 = lean_unbox(x_44);
lean_ctor_set_uint8(x_69, sizeof(void*)*7 + 9, x_71);
x_72 = lean_unbox(x_44);
lean_ctor_set_uint8(x_69, sizeof(void*)*7 + 10, x_72);
lean_inc(x_38);
x_73 = lean_apply_5(x_1, x_69, x_38, x_3, x_4, x_39);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_get(x_38, x_75);
lean_dec(x_38);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_dec(x_38);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
lean_inc(x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_14);
lean_inc(x_14);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
lean_inc(x_14);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
lean_inc(x_15);
x_21 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_17);
lean_ctor_set(x_21, 6, x_18);
lean_ctor_set(x_21, 7, x_19);
lean_ctor_set(x_21, 8, x_20);
lean_inc(x_14);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_14);
lean_inc(x_14);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_14);
lean_inc(x_14);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_14);
lean_inc(x_14);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_14);
lean_inc(x_25);
lean_inc(x_22);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_25);
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
lean_ctor_set(x_36, 2, x_13);
lean_ctor_set(x_36, 3, x_13);
lean_ctor_set_usize(x_36, 4, x_29);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_14);
lean_inc_n(x_15, 2);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_15);
lean_ctor_set(x_38, 2, x_15);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_12);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_st_mk_ref(x_39, x_11);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(1);
x_44 = lean_box(1);
x_45 = lean_box(0);
x_46 = lean_box(2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 0, 18);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 0, x_49);
x_50 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 1, x_50);
x_51 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 2, x_51);
x_52 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 3, x_52);
x_53 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 4, x_53);
x_54 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 5, x_54);
x_55 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 6, x_55);
x_56 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 7, x_56);
x_57 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 8, x_57);
x_58 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 9, x_58);
x_59 = lean_unbox(x_45);
lean_ctor_set_uint8(x_48, 10, x_59);
x_60 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 11, x_60);
x_61 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 12, x_61);
x_62 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 13, x_62);
x_63 = lean_unbox(x_46);
lean_ctor_set_uint8(x_48, 14, x_63);
x_64 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 15, x_64);
x_65 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 16, x_65);
x_66 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 17, x_66);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_48);
x_68 = lean_ctor_get(x_10, 0);
lean_inc(x_68);
lean_dec(x_10);
x_69 = lean_mk_empty_array_with_capacity(x_13);
x_70 = lean_box(0);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_12);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_69);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_13);
lean_ctor_set(x_72, 6, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*7, x_67);
x_73 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 8, x_73);
x_74 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 9, x_74);
x_75 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 10, x_75);
lean_inc(x_41);
x_76 = lean_apply_5(x_2, x_72, x_41, x_6, x_7, x_42);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_st_ref_get(x_41, x_78);
lean_dec(x_41);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_dec(x_41);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Compiler_LCNF_mkAuxParam(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_13, x_2, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_array_get_size(x_38);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_dec(x_37);
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_36;
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_1, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_object* x_45; 
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_8);
return x_45;
}
}
}
else
{
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_36;
}
block_36:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_2, x_11, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_18 = l_Lean_Compiler_LCNF_LetValue_inferType(x_1, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Compiler_LCNF_mkLetDecl(x_16, x_19, x_1, x_10, x_11, x_12, x_13, x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_24, x_9, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
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
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_8 = x_22;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
goto block_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_23 = lean_box(1);
x_24 = lean_mk_string_unchecked("_x", 2, 2);
x_25 = l_Lean_Name_mkStr1(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_23, x_25, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_8 = x_27;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_28;
goto block_21;
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 4);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_8);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode(x_18, x_19, x_10, x_11, x_12, x_13, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_7 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_unsigned_to_nat(5u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_nat_pow(x_9, x_12);
lean_dec(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = lean_usize_to_nat(x_14);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_usize(x_19, 4, x_11);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_7);
x_23 = lean_unsigned_to_nat(8u);
x_24 = lean_nat_shiftl(x_23, x_9);
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_nat_div(x_24, x_25);
lean_dec(x_24);
x_27 = l_Nat_nextPowerOfTwo(x_26);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_empty_array_with_capacity(x_18);
lean_inc(x_30);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_20);
x_33 = lean_st_mk_ref(x_32, x_6);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_34);
x_36 = lean_apply_6(x_1, x_34, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_34, x_38);
lean_dec(x_34);
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
lean_dec(x_34);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
case 3:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_1);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
case 7:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 2);
x_2 = x_7;
goto _start;
}
case 8:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_1);
x_9 = lean_box(2);
x_10 = lean_unbox(x_9);
return x_10;
}
case 10:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_2, 1);
x_2 = x_11;
goto _start;
}
default: 
{
lean_object* x_13; 
x_13 = l_Lean_Expr_getAppFn(x_2);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Environment_find_x3f(x_1, x_16, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(2);
x_21 = lean_unbox(x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_22);
x_25 = lean_box(2);
x_26 = lean_unbox(x_25);
return x_26;
}
}
}
default: 
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_1);
x_27 = lean_box(2);
x_28 = lean_unbox(x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_24; lean_object* x_25; lean_object* x_113; uint8_t x_114; 
x_113 = lean_st_ref_get(x_4, x_5);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_ctor_get(x_113, 1);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_117, x_1);
switch (x_118) {
case 0:
{
lean_object* x_119; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_119 = lean_box(0);
lean_ctor_set(x_113, 0, x_119);
return x_113;
}
case 1:
{
lean_object* x_120; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_120 = lean_box(1);
lean_ctor_set(x_113, 0, x_120);
return x_113;
}
default: 
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_free_object(x_113);
x_121 = lean_st_ref_get(x_2, x_116);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 3);
lean_inc(x_123);
lean_dec(x_122);
x_124 = !lean_is_exclusive(x_121);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; lean_object* x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; lean_object* x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; size_t x_138; size_t x_139; lean_object* x_140; size_t x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; 
x_125 = lean_ctor_get(x_121, 1);
x_126 = lean_ctor_get(x_121, 0);
lean_dec(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
lean_dec(x_123);
x_128 = lean_array_get_size(x_127);
x_129 = l_Lean_Expr_hash(x_1);
x_130 = lean_unsigned_to_nat(32u);
x_131 = lean_uint64_of_nat(x_130);
x_132 = lean_uint64_shift_right(x_129, x_131);
x_133 = lean_uint64_xor(x_129, x_132);
x_134 = lean_unsigned_to_nat(16u);
x_135 = lean_uint64_of_nat(x_134);
x_136 = lean_uint64_shift_right(x_133, x_135);
x_137 = lean_uint64_xor(x_133, x_136);
x_138 = lean_uint64_to_usize(x_137);
x_139 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_usize_of_nat(x_140);
x_142 = lean_usize_sub(x_139, x_141);
x_143 = lean_usize_land(x_138, x_142);
x_144 = lean_array_uget(x_127, x_143);
lean_dec(x_127);
x_145 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__3___redArg(x_1, x_144);
lean_dec(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; size_t x_166; lean_object* x_167; lean_object* x_168; size_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint64_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; lean_object* x_213; 
lean_free_object(x_121);
x_146 = lean_st_ref_get(x_2, x_125);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_box(0);
x_150 = lean_unsigned_to_nat(0u);
x_151 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_151);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
lean_inc(x_151);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_151);
lean_inc(x_151);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_151);
lean_inc(x_151);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_151);
lean_inc(x_151);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_151);
lean_inc(x_151);
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_151);
lean_inc(x_152);
x_158 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_158, 0, x_150);
lean_ctor_set(x_158, 1, x_150);
lean_ctor_set(x_158, 2, x_150);
lean_ctor_set(x_158, 3, x_152);
lean_ctor_set(x_158, 4, x_153);
lean_ctor_set(x_158, 5, x_154);
lean_ctor_set(x_158, 6, x_155);
lean_ctor_set(x_158, 7, x_156);
lean_ctor_set(x_158, 8, x_157);
lean_inc(x_151);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_151);
lean_inc(x_151);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_151);
lean_inc(x_151);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_151);
lean_inc(x_151);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_151);
lean_inc(x_162);
lean_inc(x_159);
x_163 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_160);
lean_ctor_set(x_163, 2, x_161);
lean_ctor_set(x_163, 3, x_159);
lean_ctor_set(x_163, 4, x_162);
lean_ctor_set(x_163, 5, x_162);
x_164 = lean_unsigned_to_nat(2u);
x_165 = lean_unsigned_to_nat(5u);
x_166 = lean_usize_of_nat(x_165);
x_167 = lean_usize_to_nat(x_166);
x_168 = lean_nat_pow(x_164, x_167);
lean_dec(x_167);
x_169 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_170 = lean_usize_to_nat(x_169);
x_171 = lean_mk_empty_array_with_capacity(x_170);
lean_dec(x_170);
lean_inc(x_171);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
lean_ctor_set(x_173, 2, x_150);
lean_ctor_set(x_173, 3, x_150);
lean_ctor_set_usize(x_173, 4, x_166);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_151);
lean_inc_n(x_152, 2);
x_175 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_175, 0, x_152);
lean_ctor_set(x_175, 1, x_152);
lean_ctor_set(x_175, 2, x_152);
lean_ctor_set(x_175, 3, x_174);
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_158);
lean_ctor_set(x_176, 1, x_163);
lean_ctor_set(x_176, 2, x_149);
lean_ctor_set(x_176, 3, x_173);
lean_ctor_set(x_176, 4, x_175);
x_177 = lean_st_mk_ref(x_176, x_148);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_box(1);
x_181 = lean_box(1);
x_182 = lean_box(0);
x_183 = lean_box(2);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 0, 18);
x_186 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, 0, x_186);
x_187 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, 1, x_187);
x_188 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, 2, x_188);
x_189 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, 3, x_189);
x_190 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, 4, x_190);
x_191 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 5, x_191);
x_192 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 6, x_192);
x_193 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, 7, x_193);
x_194 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 8, x_194);
x_195 = lean_unbox(x_181);
lean_ctor_set_uint8(x_185, 9, x_195);
x_196 = lean_unbox(x_182);
lean_ctor_set_uint8(x_185, 10, x_196);
x_197 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 11, x_197);
x_198 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 12, x_198);
x_199 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 13, x_199);
x_200 = lean_unbox(x_183);
lean_ctor_set_uint8(x_185, 14, x_200);
x_201 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 15, x_201);
x_202 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 16, x_202);
x_203 = lean_unbox(x_180);
lean_ctor_set_uint8(x_185, 17, x_203);
x_204 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_185);
x_205 = lean_ctor_get(x_147, 0);
lean_inc(x_205);
lean_dec(x_147);
x_206 = lean_mk_empty_array_with_capacity(x_150);
x_207 = lean_box(0);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_209, 0, x_185);
lean_ctor_set(x_209, 1, x_149);
lean_ctor_set(x_209, 2, x_205);
lean_ctor_set(x_209, 3, x_206);
lean_ctor_set(x_209, 4, x_207);
lean_ctor_set(x_209, 5, x_150);
lean_ctor_set(x_209, 6, x_208);
lean_ctor_set_uint64(x_209, sizeof(void*)*7, x_204);
x_210 = lean_unbox(x_184);
lean_ctor_set_uint8(x_209, sizeof(void*)*7 + 8, x_210);
x_211 = lean_unbox(x_184);
lean_ctor_set_uint8(x_209, sizeof(void*)*7 + 9, x_211);
x_212 = lean_unbox(x_184);
lean_ctor_set_uint8(x_209, sizeof(void*)*7 + 10, x_212);
lean_inc(x_178);
lean_inc(x_1);
x_213 = l_Lean_Meta_isTypeFormerType(x_1, x_209, x_178, x_3, x_4, x_179);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_st_ref_get(x_178, x_215);
lean_dec(x_178);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_unbox(x_214);
lean_dec(x_214);
x_24 = x_218;
x_25 = x_217;
goto block_112;
}
else
{
lean_dec(x_178);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_213, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_213, 1);
lean_inc(x_220);
lean_dec(x_213);
x_221 = lean_unbox(x_219);
lean_dec(x_219);
x_24 = x_221;
x_25 = x_220;
goto block_112;
}
else
{
lean_dec(x_1);
return x_213;
}
}
}
else
{
lean_object* x_222; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = lean_ctor_get(x_145, 0);
lean_inc(x_222);
lean_dec(x_145);
lean_ctor_set(x_121, 0, x_222);
return x_121;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint64_t x_226; lean_object* x_227; uint64_t x_228; uint64_t x_229; uint64_t x_230; lean_object* x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; size_t x_235; size_t x_236; lean_object* x_237; size_t x_238; size_t x_239; size_t x_240; lean_object* x_241; lean_object* x_242; 
x_223 = lean_ctor_get(x_121, 1);
lean_inc(x_223);
lean_dec(x_121);
x_224 = lean_ctor_get(x_123, 1);
lean_inc(x_224);
lean_dec(x_123);
x_225 = lean_array_get_size(x_224);
x_226 = l_Lean_Expr_hash(x_1);
x_227 = lean_unsigned_to_nat(32u);
x_228 = lean_uint64_of_nat(x_227);
x_229 = lean_uint64_shift_right(x_226, x_228);
x_230 = lean_uint64_xor(x_226, x_229);
x_231 = lean_unsigned_to_nat(16u);
x_232 = lean_uint64_of_nat(x_231);
x_233 = lean_uint64_shift_right(x_230, x_232);
x_234 = lean_uint64_xor(x_230, x_233);
x_235 = lean_uint64_to_usize(x_234);
x_236 = lean_usize_of_nat(x_225);
lean_dec(x_225);
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_usize_of_nat(x_237);
x_239 = lean_usize_sub(x_236, x_238);
x_240 = lean_usize_land(x_235, x_239);
x_241 = lean_array_uget(x_224, x_240);
lean_dec(x_224);
x_242 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__3___redArg(x_1, x_241);
lean_dec(x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; size_t x_263; lean_object* x_264; lean_object* x_265; size_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; uint8_t x_284; uint8_t x_285; uint8_t x_286; uint8_t x_287; uint8_t x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; uint8_t x_294; uint8_t x_295; uint8_t x_296; uint8_t x_297; uint8_t x_298; uint8_t x_299; uint8_t x_300; uint64_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; uint8_t x_309; lean_object* x_310; 
x_243 = lean_st_ref_get(x_2, x_223);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_box(0);
x_247 = lean_unsigned_to_nat(0u);
x_248 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_248);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
lean_inc(x_248);
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_248);
lean_inc(x_248);
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_248);
lean_inc(x_248);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_248);
lean_inc(x_248);
x_253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_253, 0, x_248);
lean_inc(x_248);
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_248);
lean_inc(x_249);
x_255 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_255, 0, x_247);
lean_ctor_set(x_255, 1, x_247);
lean_ctor_set(x_255, 2, x_247);
lean_ctor_set(x_255, 3, x_249);
lean_ctor_set(x_255, 4, x_250);
lean_ctor_set(x_255, 5, x_251);
lean_ctor_set(x_255, 6, x_252);
lean_ctor_set(x_255, 7, x_253);
lean_ctor_set(x_255, 8, x_254);
lean_inc(x_248);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_248);
lean_inc(x_248);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_248);
lean_inc(x_248);
x_258 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_258, 0, x_248);
lean_inc(x_248);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_248);
lean_inc(x_259);
lean_inc(x_256);
x_260 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_257);
lean_ctor_set(x_260, 2, x_258);
lean_ctor_set(x_260, 3, x_256);
lean_ctor_set(x_260, 4, x_259);
lean_ctor_set(x_260, 5, x_259);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_unsigned_to_nat(5u);
x_263 = lean_usize_of_nat(x_262);
x_264 = lean_usize_to_nat(x_263);
x_265 = lean_nat_pow(x_261, x_264);
lean_dec(x_264);
x_266 = lean_usize_of_nat(x_265);
lean_dec(x_265);
x_267 = lean_usize_to_nat(x_266);
x_268 = lean_mk_empty_array_with_capacity(x_267);
lean_dec(x_267);
lean_inc(x_268);
x_269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
lean_ctor_set(x_270, 2, x_247);
lean_ctor_set(x_270, 3, x_247);
lean_ctor_set_usize(x_270, 4, x_263);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_248);
lean_inc_n(x_249, 2);
x_272 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_272, 0, x_249);
lean_ctor_set(x_272, 1, x_249);
lean_ctor_set(x_272, 2, x_249);
lean_ctor_set(x_272, 3, x_271);
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_255);
lean_ctor_set(x_273, 1, x_260);
lean_ctor_set(x_273, 2, x_246);
lean_ctor_set(x_273, 3, x_270);
lean_ctor_set(x_273, 4, x_272);
x_274 = lean_st_mk_ref(x_273, x_245);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = lean_box(1);
x_278 = lean_box(1);
x_279 = lean_box(0);
x_280 = lean_box(2);
x_281 = lean_box(0);
x_282 = lean_alloc_ctor(0, 0, 18);
x_283 = lean_unbox(x_281);
lean_ctor_set_uint8(x_282, 0, x_283);
x_284 = lean_unbox(x_281);
lean_ctor_set_uint8(x_282, 1, x_284);
x_285 = lean_unbox(x_281);
lean_ctor_set_uint8(x_282, 2, x_285);
x_286 = lean_unbox(x_281);
lean_ctor_set_uint8(x_282, 3, x_286);
x_287 = lean_unbox(x_281);
lean_ctor_set_uint8(x_282, 4, x_287);
x_288 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 5, x_288);
x_289 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 6, x_289);
x_290 = lean_unbox(x_281);
lean_ctor_set_uint8(x_282, 7, x_290);
x_291 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 8, x_291);
x_292 = lean_unbox(x_278);
lean_ctor_set_uint8(x_282, 9, x_292);
x_293 = lean_unbox(x_279);
lean_ctor_set_uint8(x_282, 10, x_293);
x_294 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 11, x_294);
x_295 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 12, x_295);
x_296 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 13, x_296);
x_297 = lean_unbox(x_280);
lean_ctor_set_uint8(x_282, 14, x_297);
x_298 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 15, x_298);
x_299 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 16, x_299);
x_300 = lean_unbox(x_277);
lean_ctor_set_uint8(x_282, 17, x_300);
x_301 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_282);
x_302 = lean_ctor_get(x_244, 0);
lean_inc(x_302);
lean_dec(x_244);
x_303 = lean_mk_empty_array_with_capacity(x_247);
x_304 = lean_box(0);
x_305 = lean_box(0);
x_306 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_306, 0, x_282);
lean_ctor_set(x_306, 1, x_246);
lean_ctor_set(x_306, 2, x_302);
lean_ctor_set(x_306, 3, x_303);
lean_ctor_set(x_306, 4, x_304);
lean_ctor_set(x_306, 5, x_247);
lean_ctor_set(x_306, 6, x_305);
lean_ctor_set_uint64(x_306, sizeof(void*)*7, x_301);
x_307 = lean_unbox(x_281);
lean_ctor_set_uint8(x_306, sizeof(void*)*7 + 8, x_307);
x_308 = lean_unbox(x_281);
lean_ctor_set_uint8(x_306, sizeof(void*)*7 + 9, x_308);
x_309 = lean_unbox(x_281);
lean_ctor_set_uint8(x_306, sizeof(void*)*7 + 10, x_309);
lean_inc(x_275);
lean_inc(x_1);
x_310 = l_Lean_Meta_isTypeFormerType(x_1, x_306, x_275, x_3, x_4, x_276);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_st_ref_get(x_275, x_312);
lean_dec(x_275);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_unbox(x_311);
lean_dec(x_311);
x_24 = x_315;
x_25 = x_314;
goto block_112;
}
else
{
lean_dec(x_275);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_310, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_310, 1);
lean_inc(x_317);
lean_dec(x_310);
x_318 = lean_unbox(x_316);
lean_dec(x_316);
x_24 = x_318;
x_25 = x_317;
goto block_112;
}
else
{
lean_dec(x_1);
return x_310;
}
}
}
else
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_319 = lean_ctor_get(x_242, 0);
lean_inc(x_319);
lean_dec(x_242);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_223);
return x_320;
}
}
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_321 = lean_ctor_get(x_113, 0);
x_322 = lean_ctor_get(x_113, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_113);
x_323 = lean_ctor_get(x_321, 0);
lean_inc(x_323);
lean_dec(x_321);
x_324 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_323, x_1);
switch (x_324) {
case 0:
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_325 = lean_box(0);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_322);
return x_326;
}
case 1:
{
lean_object* x_327; lean_object* x_328; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_327 = lean_box(1);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_322);
return x_328;
}
default: 
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint64_t x_336; lean_object* x_337; uint64_t x_338; uint64_t x_339; uint64_t x_340; lean_object* x_341; uint64_t x_342; uint64_t x_343; uint64_t x_344; size_t x_345; size_t x_346; lean_object* x_347; size_t x_348; size_t x_349; size_t x_350; lean_object* x_351; lean_object* x_352; 
x_329 = lean_st_ref_get(x_2, x_322);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_330, 3);
lean_inc(x_331);
lean_dec(x_330);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_333 = x_329;
} else {
 lean_dec_ref(x_329);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
lean_dec(x_331);
x_335 = lean_array_get_size(x_334);
x_336 = l_Lean_Expr_hash(x_1);
x_337 = lean_unsigned_to_nat(32u);
x_338 = lean_uint64_of_nat(x_337);
x_339 = lean_uint64_shift_right(x_336, x_338);
x_340 = lean_uint64_xor(x_336, x_339);
x_341 = lean_unsigned_to_nat(16u);
x_342 = lean_uint64_of_nat(x_341);
x_343 = lean_uint64_shift_right(x_340, x_342);
x_344 = lean_uint64_xor(x_340, x_343);
x_345 = lean_uint64_to_usize(x_344);
x_346 = lean_usize_of_nat(x_335);
lean_dec(x_335);
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_usize_of_nat(x_347);
x_349 = lean_usize_sub(x_346, x_348);
x_350 = lean_usize_land(x_345, x_349);
x_351 = lean_array_uget(x_334, x_350);
lean_dec(x_334);
x_352 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__3___redArg(x_1, x_351);
lean_dec(x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; size_t x_373; lean_object* x_374; lean_object* x_375; size_t x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; uint8_t x_394; uint8_t x_395; uint8_t x_396; uint8_t x_397; uint8_t x_398; uint8_t x_399; uint8_t x_400; uint8_t x_401; uint8_t x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; uint8_t x_406; uint8_t x_407; uint8_t x_408; uint8_t x_409; uint8_t x_410; uint64_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; uint8_t x_418; uint8_t x_419; lean_object* x_420; 
lean_dec(x_333);
x_353 = lean_st_ref_get(x_2, x_332);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_box(0);
x_357 = lean_unsigned_to_nat(0u);
x_358 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_358);
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_358);
lean_inc(x_358);
x_360 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_360, 0, x_358);
lean_inc(x_358);
x_361 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_361, 0, x_358);
lean_inc(x_358);
x_362 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_362, 0, x_358);
lean_inc(x_358);
x_363 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_363, 0, x_358);
lean_inc(x_358);
x_364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_364, 0, x_358);
lean_inc(x_359);
x_365 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_365, 0, x_357);
lean_ctor_set(x_365, 1, x_357);
lean_ctor_set(x_365, 2, x_357);
lean_ctor_set(x_365, 3, x_359);
lean_ctor_set(x_365, 4, x_360);
lean_ctor_set(x_365, 5, x_361);
lean_ctor_set(x_365, 6, x_362);
lean_ctor_set(x_365, 7, x_363);
lean_ctor_set(x_365, 8, x_364);
lean_inc(x_358);
x_366 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_366, 0, x_358);
lean_inc(x_358);
x_367 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_367, 0, x_358);
lean_inc(x_358);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_358);
lean_inc(x_358);
x_369 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_369, 0, x_358);
lean_inc(x_369);
lean_inc(x_366);
x_370 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_370, 0, x_366);
lean_ctor_set(x_370, 1, x_367);
lean_ctor_set(x_370, 2, x_368);
lean_ctor_set(x_370, 3, x_366);
lean_ctor_set(x_370, 4, x_369);
lean_ctor_set(x_370, 5, x_369);
x_371 = lean_unsigned_to_nat(2u);
x_372 = lean_unsigned_to_nat(5u);
x_373 = lean_usize_of_nat(x_372);
x_374 = lean_usize_to_nat(x_373);
x_375 = lean_nat_pow(x_371, x_374);
lean_dec(x_374);
x_376 = lean_usize_of_nat(x_375);
lean_dec(x_375);
x_377 = lean_usize_to_nat(x_376);
x_378 = lean_mk_empty_array_with_capacity(x_377);
lean_dec(x_377);
lean_inc(x_378);
x_379 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_379, 0, x_378);
x_380 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_378);
lean_ctor_set(x_380, 2, x_357);
lean_ctor_set(x_380, 3, x_357);
lean_ctor_set_usize(x_380, 4, x_373);
x_381 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_381, 0, x_358);
lean_inc_n(x_359, 2);
x_382 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_382, 0, x_359);
lean_ctor_set(x_382, 1, x_359);
lean_ctor_set(x_382, 2, x_359);
lean_ctor_set(x_382, 3, x_381);
x_383 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_383, 0, x_365);
lean_ctor_set(x_383, 1, x_370);
lean_ctor_set(x_383, 2, x_356);
lean_ctor_set(x_383, 3, x_380);
lean_ctor_set(x_383, 4, x_382);
x_384 = lean_st_mk_ref(x_383, x_355);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_box(1);
x_388 = lean_box(1);
x_389 = lean_box(0);
x_390 = lean_box(2);
x_391 = lean_box(0);
x_392 = lean_alloc_ctor(0, 0, 18);
x_393 = lean_unbox(x_391);
lean_ctor_set_uint8(x_392, 0, x_393);
x_394 = lean_unbox(x_391);
lean_ctor_set_uint8(x_392, 1, x_394);
x_395 = lean_unbox(x_391);
lean_ctor_set_uint8(x_392, 2, x_395);
x_396 = lean_unbox(x_391);
lean_ctor_set_uint8(x_392, 3, x_396);
x_397 = lean_unbox(x_391);
lean_ctor_set_uint8(x_392, 4, x_397);
x_398 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 5, x_398);
x_399 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 6, x_399);
x_400 = lean_unbox(x_391);
lean_ctor_set_uint8(x_392, 7, x_400);
x_401 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 8, x_401);
x_402 = lean_unbox(x_388);
lean_ctor_set_uint8(x_392, 9, x_402);
x_403 = lean_unbox(x_389);
lean_ctor_set_uint8(x_392, 10, x_403);
x_404 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 11, x_404);
x_405 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 12, x_405);
x_406 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 13, x_406);
x_407 = lean_unbox(x_390);
lean_ctor_set_uint8(x_392, 14, x_407);
x_408 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 15, x_408);
x_409 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 16, x_409);
x_410 = lean_unbox(x_387);
lean_ctor_set_uint8(x_392, 17, x_410);
x_411 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_392);
x_412 = lean_ctor_get(x_354, 0);
lean_inc(x_412);
lean_dec(x_354);
x_413 = lean_mk_empty_array_with_capacity(x_357);
x_414 = lean_box(0);
x_415 = lean_box(0);
x_416 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_416, 0, x_392);
lean_ctor_set(x_416, 1, x_356);
lean_ctor_set(x_416, 2, x_412);
lean_ctor_set(x_416, 3, x_413);
lean_ctor_set(x_416, 4, x_414);
lean_ctor_set(x_416, 5, x_357);
lean_ctor_set(x_416, 6, x_415);
lean_ctor_set_uint64(x_416, sizeof(void*)*7, x_411);
x_417 = lean_unbox(x_391);
lean_ctor_set_uint8(x_416, sizeof(void*)*7 + 8, x_417);
x_418 = lean_unbox(x_391);
lean_ctor_set_uint8(x_416, sizeof(void*)*7 + 9, x_418);
x_419 = lean_unbox(x_391);
lean_ctor_set_uint8(x_416, sizeof(void*)*7 + 10, x_419);
lean_inc(x_385);
lean_inc(x_1);
x_420 = l_Lean_Meta_isTypeFormerType(x_1, x_416, x_385, x_3, x_4, x_386);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_st_ref_get(x_385, x_422);
lean_dec(x_385);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_425 = lean_unbox(x_421);
lean_dec(x_421);
x_24 = x_425;
x_25 = x_424;
goto block_112;
}
else
{
lean_dec(x_385);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_426 = lean_ctor_get(x_420, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_420, 1);
lean_inc(x_427);
lean_dec(x_420);
x_428 = lean_unbox(x_426);
lean_dec(x_426);
x_24 = x_428;
x_25 = x_427;
goto block_112;
}
else
{
lean_dec(x_1);
return x_420;
}
}
}
else
{
lean_object* x_429; lean_object* x_430; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_429 = lean_ctor_get(x_352, 0);
lean_inc(x_429);
lean_dec(x_352);
if (lean_is_scalar(x_333)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_333;
}
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_332);
return x_430;
}
}
}
}
block_23:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
x_16 = lean_st_ref_set(x_2, x_15, x_9);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(x_11);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(x_11);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
block_112:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_st_ref_take(x_2, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 2);
lean_inc(x_35);
x_36 = lean_array_get_size(x_32);
x_37 = l_Lean_Expr_hash(x_1);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_32, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_nat_add(x_31, x_48);
lean_dec(x_31);
x_55 = lean_box(x_24);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_32, x_51, x_56);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_nat_shiftl(x_54, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_57);
lean_ctor_set(x_28, 1, x_64);
lean_ctor_set(x_28, 0, x_54);
x_6 = x_27;
x_7 = x_35;
x_8 = x_34;
x_9 = x_29;
x_10 = x_33;
x_11 = x_24;
x_12 = x_28;
goto block_23;
}
else
{
lean_ctor_set(x_28, 1, x_57);
lean_ctor_set(x_28, 0, x_54);
x_6 = x_27;
x_7 = x_35;
x_8 = x_34;
x_9 = x_29;
x_10 = x_33;
x_11 = x_24;
x_12 = x_28;
goto block_23;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_box(0);
x_66 = lean_array_uset(x_32, x_51, x_65);
x_67 = lean_box(x_24);
x_68 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(x_1, x_67, x_52);
x_69 = lean_array_uset(x_66, x_51, x_68);
lean_ctor_set(x_28, 1, x_69);
x_6 = x_27;
x_7 = x_35;
x_8 = x_34;
x_9 = x_29;
x_10 = x_33;
x_11 = x_24;
x_12 = x_28;
goto block_23;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; size_t x_85; size_t x_86; lean_object* x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; uint8_t x_92; 
x_70 = lean_ctor_get(x_28, 0);
x_71 = lean_ctor_get(x_28, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_28);
x_72 = lean_ctor_get(x_27, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_27, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_27, 2);
lean_inc(x_74);
x_75 = lean_array_get_size(x_71);
x_76 = l_Lean_Expr_hash(x_1);
x_77 = lean_unsigned_to_nat(32u);
x_78 = lean_uint64_of_nat(x_77);
x_79 = lean_uint64_shift_right(x_76, x_78);
x_80 = lean_uint64_xor(x_76, x_79);
x_81 = lean_unsigned_to_nat(16u);
x_82 = lean_uint64_of_nat(x_81);
x_83 = lean_uint64_shift_right(x_80, x_82);
x_84 = lean_uint64_xor(x_80, x_83);
x_85 = lean_uint64_to_usize(x_84);
x_86 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_usize_of_nat(x_87);
x_89 = lean_usize_sub(x_86, x_88);
x_90 = lean_usize_land(x_85, x_89);
x_91 = lean_array_uget(x_71, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_93 = lean_nat_add(x_70, x_87);
lean_dec(x_70);
x_94 = lean_box(x_24);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_91);
x_96 = lean_array_uset(x_71, x_90, x_95);
x_97 = lean_unsigned_to_nat(2u);
x_98 = lean_nat_shiftl(x_93, x_97);
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
x_103 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_96);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_93);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_27;
x_7 = x_74;
x_8 = x_73;
x_9 = x_29;
x_10 = x_72;
x_11 = x_24;
x_12 = x_104;
goto block_23;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_96);
x_6 = x_27;
x_7 = x_74;
x_8 = x_73;
x_9 = x_29;
x_10 = x_72;
x_11 = x_24;
x_12 = x_105;
goto block_23;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_box(0);
x_107 = lean_array_uset(x_71, x_90, x_106);
x_108 = lean_box(x_24);
x_109 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(x_1, x_108, x_91);
x_110 = lean_array_uset(x_107, x_90, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_70);
lean_ctor_set(x_111, 1, x_110);
x_6 = x_27;
x_7 = x_74;
x_8 = x_73;
x_9 = x_29;
x_10 = x_72;
x_11 = x_24;
x_12 = x_111;
goto block_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_st_ref_get(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_12, 3);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_4);
lean_ctor_set(x_16, 5, x_5);
x_17 = lean_st_ref_set(x_1, x_16, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_2, x_10);
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
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_ctor_get(x_12, 5);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_17);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set(x_21, 5, x_20);
x_22 = lean_st_ref_set(x_2, x_21, x_13);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_9, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 5);
lean_inc(x_27);
lean_dec(x_9);
lean_inc(x_2);
x_28 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_24, x_25, x_26, x_27, x_31, x_30);
lean_dec(x_31);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_29);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_24, x_25, x_26, x_27, x_39, x_38);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_37);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_3);
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = l_Lean_Compiler_LCNF_anyExpr;
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 5);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_replace_expr(x_8, x_1);
lean_dec(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 5);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_replace_expr(x_13, x_1);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_22; lean_object* x_23; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_st_ref_get(x_2, x_5);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 2);
lean_inc(x_110);
lean_dec(x_109);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint64_t x_116; lean_object* x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; lean_object* x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; size_t x_125; size_t x_126; lean_object* x_127; size_t x_128; size_t x_129; size_t x_130; lean_object* x_131; lean_object* x_132; 
x_112 = lean_ctor_get(x_108, 1);
x_113 = lean_ctor_get(x_108, 0);
lean_dec(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_array_get_size(x_114);
x_116 = l_Lean_Expr_hash(x_1);
x_117 = lean_unsigned_to_nat(32u);
x_118 = lean_uint64_of_nat(x_117);
x_119 = lean_uint64_shift_right(x_116, x_118);
x_120 = lean_uint64_xor(x_116, x_119);
x_121 = lean_unsigned_to_nat(16u);
x_122 = lean_uint64_of_nat(x_121);
x_123 = lean_uint64_shift_right(x_120, x_122);
x_124 = lean_uint64_xor(x_120, x_123);
x_125 = lean_uint64_to_usize(x_124);
x_126 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_usize_of_nat(x_127);
x_129 = lean_usize_sub(x_126, x_128);
x_130 = lean_usize_land(x_125, x_129);
x_131 = lean_array_uget(x_114, x_130);
lean_dec(x_114);
x_132 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__3___redArg(x_1, x_131);
lean_dec(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; size_t x_153; lean_object* x_154; lean_object* x_155; size_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint64_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; lean_object* x_200; 
lean_free_object(x_108);
x_133 = lean_st_ref_get(x_2, x_112);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_box(0);
x_137 = lean_unsigned_to_nat(0u);
x_138 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_138);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_138);
lean_inc(x_138);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_138);
lean_inc(x_138);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_138);
lean_inc(x_138);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_138);
lean_inc(x_138);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_138);
lean_inc(x_138);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_138);
lean_inc(x_139);
x_145 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_137);
lean_ctor_set(x_145, 2, x_137);
lean_ctor_set(x_145, 3, x_139);
lean_ctor_set(x_145, 4, x_140);
lean_ctor_set(x_145, 5, x_141);
lean_ctor_set(x_145, 6, x_142);
lean_ctor_set(x_145, 7, x_143);
lean_ctor_set(x_145, 8, x_144);
lean_inc(x_138);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_138);
lean_inc(x_138);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_138);
lean_inc(x_138);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_138);
lean_inc(x_138);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_138);
lean_inc(x_149);
lean_inc(x_146);
x_150 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_147);
lean_ctor_set(x_150, 2, x_148);
lean_ctor_set(x_150, 3, x_146);
lean_ctor_set(x_150, 4, x_149);
lean_ctor_set(x_150, 5, x_149);
x_151 = lean_unsigned_to_nat(2u);
x_152 = lean_unsigned_to_nat(5u);
x_153 = lean_usize_of_nat(x_152);
x_154 = lean_usize_to_nat(x_153);
x_155 = lean_nat_pow(x_151, x_154);
lean_dec(x_154);
x_156 = lean_usize_of_nat(x_155);
lean_dec(x_155);
x_157 = lean_usize_to_nat(x_156);
x_158 = lean_mk_empty_array_with_capacity(x_157);
lean_dec(x_157);
lean_inc(x_158);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_160, 2, x_137);
lean_ctor_set(x_160, 3, x_137);
lean_ctor_set_usize(x_160, 4, x_153);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_138);
lean_inc_n(x_139, 2);
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_139);
lean_ctor_set(x_162, 1, x_139);
lean_ctor_set(x_162, 2, x_139);
lean_ctor_set(x_162, 3, x_161);
x_163 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_163, 0, x_145);
lean_ctor_set(x_163, 1, x_150);
lean_ctor_set(x_163, 2, x_136);
lean_ctor_set(x_163, 3, x_160);
lean_ctor_set(x_163, 4, x_162);
x_164 = lean_st_mk_ref(x_163, x_135);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_box(1);
x_168 = lean_box(1);
x_169 = lean_box(0);
x_170 = lean_box(2);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(0, 0, 18);
x_173 = lean_unbox(x_171);
lean_ctor_set_uint8(x_172, 0, x_173);
x_174 = lean_unbox(x_171);
lean_ctor_set_uint8(x_172, 1, x_174);
x_175 = lean_unbox(x_171);
lean_ctor_set_uint8(x_172, 2, x_175);
x_176 = lean_unbox(x_171);
lean_ctor_set_uint8(x_172, 3, x_176);
x_177 = lean_unbox(x_171);
lean_ctor_set_uint8(x_172, 4, x_177);
x_178 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 5, x_178);
x_179 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 6, x_179);
x_180 = lean_unbox(x_171);
lean_ctor_set_uint8(x_172, 7, x_180);
x_181 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 8, x_181);
x_182 = lean_unbox(x_168);
lean_ctor_set_uint8(x_172, 9, x_182);
x_183 = lean_unbox(x_169);
lean_ctor_set_uint8(x_172, 10, x_183);
x_184 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 11, x_184);
x_185 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 12, x_185);
x_186 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 13, x_186);
x_187 = lean_unbox(x_170);
lean_ctor_set_uint8(x_172, 14, x_187);
x_188 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 15, x_188);
x_189 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 16, x_189);
x_190 = lean_unbox(x_167);
lean_ctor_set_uint8(x_172, 17, x_190);
x_191 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_172);
x_192 = lean_ctor_get(x_134, 0);
lean_inc(x_192);
lean_dec(x_134);
x_193 = lean_mk_empty_array_with_capacity(x_137);
x_194 = lean_box(0);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_196, 0, x_172);
lean_ctor_set(x_196, 1, x_136);
lean_ctor_set(x_196, 2, x_192);
lean_ctor_set(x_196, 3, x_193);
lean_ctor_set(x_196, 4, x_194);
lean_ctor_set(x_196, 5, x_137);
lean_ctor_set(x_196, 6, x_195);
lean_ctor_set_uint64(x_196, sizeof(void*)*7, x_191);
x_197 = lean_unbox(x_171);
lean_ctor_set_uint8(x_196, sizeof(void*)*7 + 8, x_197);
x_198 = lean_unbox(x_171);
lean_ctor_set_uint8(x_196, sizeof(void*)*7 + 9, x_198);
x_199 = lean_unbox(x_171);
lean_ctor_set_uint8(x_196, sizeof(void*)*7 + 10, x_199);
lean_inc(x_165);
lean_inc(x_1);
x_200 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_196, x_165, x_3, x_4, x_166);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_st_ref_get(x_165, x_202);
lean_dec(x_165);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_22 = x_201;
x_23 = x_204;
goto block_107;
}
else
{
lean_dec(x_165);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_200, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 1);
lean_inc(x_206);
lean_dec(x_200);
x_22 = x_205;
x_23 = x_206;
goto block_107;
}
else
{
lean_dec(x_1);
return x_200;
}
}
}
else
{
lean_object* x_207; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_207 = lean_ctor_get(x_132, 0);
lean_inc(x_207);
lean_dec(x_132);
lean_ctor_set(x_108, 0, x_207);
return x_108;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint64_t x_211; lean_object* x_212; uint64_t x_213; uint64_t x_214; uint64_t x_215; lean_object* x_216; uint64_t x_217; uint64_t x_218; uint64_t x_219; size_t x_220; size_t x_221; lean_object* x_222; size_t x_223; size_t x_224; size_t x_225; lean_object* x_226; lean_object* x_227; 
x_208 = lean_ctor_get(x_108, 1);
lean_inc(x_208);
lean_dec(x_108);
x_209 = lean_ctor_get(x_110, 1);
lean_inc(x_209);
lean_dec(x_110);
x_210 = lean_array_get_size(x_209);
x_211 = l_Lean_Expr_hash(x_1);
x_212 = lean_unsigned_to_nat(32u);
x_213 = lean_uint64_of_nat(x_212);
x_214 = lean_uint64_shift_right(x_211, x_213);
x_215 = lean_uint64_xor(x_211, x_214);
x_216 = lean_unsigned_to_nat(16u);
x_217 = lean_uint64_of_nat(x_216);
x_218 = lean_uint64_shift_right(x_215, x_217);
x_219 = lean_uint64_xor(x_215, x_218);
x_220 = lean_uint64_to_usize(x_219);
x_221 = lean_usize_of_nat(x_210);
lean_dec(x_210);
x_222 = lean_unsigned_to_nat(1u);
x_223 = lean_usize_of_nat(x_222);
x_224 = lean_usize_sub(x_221, x_223);
x_225 = lean_usize_land(x_220, x_224);
x_226 = lean_array_uget(x_209, x_225);
lean_dec(x_209);
x_227 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__3___redArg(x_1, x_226);
lean_dec(x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; size_t x_248; lean_object* x_249; lean_object* x_250; size_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; uint8_t x_285; uint64_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; uint8_t x_294; lean_object* x_295; 
x_228 = lean_st_ref_get(x_2, x_208);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_box(0);
x_232 = lean_unsigned_to_nat(0u);
x_233 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_233);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_233);
lean_inc(x_233);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_233);
lean_inc(x_233);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_233);
lean_inc(x_233);
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_233);
lean_inc(x_233);
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_233);
lean_inc(x_233);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_233);
lean_inc(x_234);
x_240 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_240, 0, x_232);
lean_ctor_set(x_240, 1, x_232);
lean_ctor_set(x_240, 2, x_232);
lean_ctor_set(x_240, 3, x_234);
lean_ctor_set(x_240, 4, x_235);
lean_ctor_set(x_240, 5, x_236);
lean_ctor_set(x_240, 6, x_237);
lean_ctor_set(x_240, 7, x_238);
lean_ctor_set(x_240, 8, x_239);
lean_inc(x_233);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_233);
lean_inc(x_233);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_233);
lean_inc(x_233);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_233);
lean_inc(x_233);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_233);
lean_inc(x_244);
lean_inc(x_241);
x_245 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_245, 0, x_241);
lean_ctor_set(x_245, 1, x_242);
lean_ctor_set(x_245, 2, x_243);
lean_ctor_set(x_245, 3, x_241);
lean_ctor_set(x_245, 4, x_244);
lean_ctor_set(x_245, 5, x_244);
x_246 = lean_unsigned_to_nat(2u);
x_247 = lean_unsigned_to_nat(5u);
x_248 = lean_usize_of_nat(x_247);
x_249 = lean_usize_to_nat(x_248);
x_250 = lean_nat_pow(x_246, x_249);
lean_dec(x_249);
x_251 = lean_usize_of_nat(x_250);
lean_dec(x_250);
x_252 = lean_usize_to_nat(x_251);
x_253 = lean_mk_empty_array_with_capacity(x_252);
lean_dec(x_252);
lean_inc(x_253);
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_253);
x_255 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
lean_ctor_set(x_255, 2, x_232);
lean_ctor_set(x_255, 3, x_232);
lean_ctor_set_usize(x_255, 4, x_248);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_233);
lean_inc_n(x_234, 2);
x_257 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_257, 0, x_234);
lean_ctor_set(x_257, 1, x_234);
lean_ctor_set(x_257, 2, x_234);
lean_ctor_set(x_257, 3, x_256);
x_258 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_258, 0, x_240);
lean_ctor_set(x_258, 1, x_245);
lean_ctor_set(x_258, 2, x_231);
lean_ctor_set(x_258, 3, x_255);
lean_ctor_set(x_258, 4, x_257);
x_259 = lean_st_mk_ref(x_258, x_230);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_box(1);
x_263 = lean_box(1);
x_264 = lean_box(0);
x_265 = lean_box(2);
x_266 = lean_box(0);
x_267 = lean_alloc_ctor(0, 0, 18);
x_268 = lean_unbox(x_266);
lean_ctor_set_uint8(x_267, 0, x_268);
x_269 = lean_unbox(x_266);
lean_ctor_set_uint8(x_267, 1, x_269);
x_270 = lean_unbox(x_266);
lean_ctor_set_uint8(x_267, 2, x_270);
x_271 = lean_unbox(x_266);
lean_ctor_set_uint8(x_267, 3, x_271);
x_272 = lean_unbox(x_266);
lean_ctor_set_uint8(x_267, 4, x_272);
x_273 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 5, x_273);
x_274 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 6, x_274);
x_275 = lean_unbox(x_266);
lean_ctor_set_uint8(x_267, 7, x_275);
x_276 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 8, x_276);
x_277 = lean_unbox(x_263);
lean_ctor_set_uint8(x_267, 9, x_277);
x_278 = lean_unbox(x_264);
lean_ctor_set_uint8(x_267, 10, x_278);
x_279 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 11, x_279);
x_280 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 12, x_280);
x_281 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 13, x_281);
x_282 = lean_unbox(x_265);
lean_ctor_set_uint8(x_267, 14, x_282);
x_283 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 15, x_283);
x_284 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 16, x_284);
x_285 = lean_unbox(x_262);
lean_ctor_set_uint8(x_267, 17, x_285);
x_286 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_267);
x_287 = lean_ctor_get(x_229, 0);
lean_inc(x_287);
lean_dec(x_229);
x_288 = lean_mk_empty_array_with_capacity(x_232);
x_289 = lean_box(0);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_291, 0, x_267);
lean_ctor_set(x_291, 1, x_231);
lean_ctor_set(x_291, 2, x_287);
lean_ctor_set(x_291, 3, x_288);
lean_ctor_set(x_291, 4, x_289);
lean_ctor_set(x_291, 5, x_232);
lean_ctor_set(x_291, 6, x_290);
lean_ctor_set_uint64(x_291, sizeof(void*)*7, x_286);
x_292 = lean_unbox(x_266);
lean_ctor_set_uint8(x_291, sizeof(void*)*7 + 8, x_292);
x_293 = lean_unbox(x_266);
lean_ctor_set_uint8(x_291, sizeof(void*)*7 + 9, x_293);
x_294 = lean_unbox(x_266);
lean_ctor_set_uint8(x_291, sizeof(void*)*7 + 10, x_294);
lean_inc(x_260);
lean_inc(x_1);
x_295 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_291, x_260, x_3, x_4, x_261);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_st_ref_get(x_260, x_297);
lean_dec(x_260);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_22 = x_296;
x_23 = x_299;
goto block_107;
}
else
{
lean_dec(x_260);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_295, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_295, 1);
lean_inc(x_301);
lean_dec(x_295);
x_22 = x_300;
x_23 = x_301;
goto block_107;
}
else
{
lean_dec(x_1);
return x_295;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_302 = lean_ctor_get(x_227, 0);
lean_inc(x_302);
lean_dec(x_227);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_208);
return x_303;
}
}
block_21:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_6, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
x_16 = lean_st_ref_set(x_2, x_15, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_7);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
block_107:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_22, x_2, x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_take(x_2, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
x_36 = lean_array_get_size(x_33);
x_37 = l_Lean_Expr_hash(x_1);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_33, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_nat_add(x_32, x_48);
lean_dec(x_32);
lean_inc(x_25);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_25);
lean_ctor_set(x_55, 2, x_52);
x_56 = lean_array_uset(x_33, x_51, x_55);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_nat_shiftl(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_56);
lean_ctor_set(x_29, 1, x_63);
lean_ctor_set(x_29, 0, x_54);
x_6 = x_28;
x_7 = x_25;
x_8 = x_30;
x_9 = x_35;
x_10 = x_34;
x_11 = x_29;
goto block_21;
}
else
{
lean_ctor_set(x_29, 1, x_56);
lean_ctor_set(x_29, 0, x_54);
x_6 = x_28;
x_7 = x_25;
x_8 = x_30;
x_9 = x_35;
x_10 = x_34;
x_11 = x_29;
goto block_21;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_box(0);
x_65 = lean_array_uset(x_33, x_51, x_64);
lean_inc(x_25);
x_66 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(x_1, x_25, x_52);
x_67 = lean_array_uset(x_65, x_51, x_66);
lean_ctor_set(x_29, 1, x_67);
x_6 = x_28;
x_7 = x_25;
x_8 = x_30;
x_9 = x_35;
x_10 = x_34;
x_11 = x_29;
goto block_21;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; size_t x_82; size_t x_83; lean_object* x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_68 = lean_ctor_get(x_29, 0);
x_69 = lean_ctor_get(x_29, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_29);
x_70 = lean_ctor_get(x_28, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_28, 1);
lean_inc(x_71);
x_72 = lean_array_get_size(x_69);
x_73 = l_Lean_Expr_hash(x_1);
x_74 = lean_unsigned_to_nat(32u);
x_75 = lean_uint64_of_nat(x_74);
x_76 = lean_uint64_shift_right(x_73, x_75);
x_77 = lean_uint64_xor(x_73, x_76);
x_78 = lean_unsigned_to_nat(16u);
x_79 = lean_uint64_of_nat(x_78);
x_80 = lean_uint64_shift_right(x_77, x_79);
x_81 = lean_uint64_xor(x_77, x_80);
x_82 = lean_uint64_to_usize(x_81);
x_83 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_usize_of_nat(x_84);
x_86 = lean_usize_sub(x_83, x_85);
x_87 = lean_usize_land(x_82, x_86);
x_88 = lean_array_uget(x_69, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_nat_add(x_68, x_84);
lean_dec(x_68);
lean_inc(x_25);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_25);
lean_ctor_set(x_91, 2, x_88);
x_92 = lean_array_uset(x_69, x_87, x_91);
x_93 = lean_unsigned_to_nat(2u);
x_94 = lean_nat_shiftl(x_90, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1(lean_box(0), x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
x_6 = x_28;
x_7 = x_25;
x_8 = x_30;
x_9 = x_71;
x_10 = x_70;
x_11 = x_100;
goto block_21;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_92);
x_6 = x_28;
x_7 = x_25;
x_8 = x_30;
x_9 = x_71;
x_10 = x_70;
x_11 = x_101;
goto block_21;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_box(0);
x_103 = lean_array_uset(x_69, x_87, x_102);
lean_inc(x_25);
x_104 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(x_1, x_25, x_88);
x_105 = lean_array_uset(x_103, x_87, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_68);
lean_ctor_set(x_106, 1, x_105);
x_6 = x_28;
x_7 = x_25;
x_8 = x_30;
x_9 = x_71;
x_10 = x_70;
x_11 = x_106;
goto block_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Name_hasMacroScopes(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_erase_macro_scopes(x_1);
x_7 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_6, x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_2, x_3, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_2);
x_15 = lean_is_marked_borrowed(x_2);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_mkParam(x_10, x_13, x_15, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_unbox(x_24);
x_27 = lean_unbox(x_25);
x_28 = l_Lean_LocalContext_mkLocalDecl(x_22, x_23, x_10, x_2, x_26, x_27);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_20, 5);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_32);
lean_ctor_set(x_34, 5, x_33);
x_35 = lean_st_ref_set(x_3, x_34, x_21);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_17);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_8, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_5, 0);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_mk_empty_array_with_capacity(x_50);
lean_inc(x_49);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 1, x_51);
lean_ctor_set(x_12, 0, x_49);
x_16 = x_12;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
goto block_48;
}
else
{
lean_object* x_52; 
lean_free_object(x_12);
x_52 = lean_box(1);
x_16 = x_52;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
goto block_48;
}
block_48:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_14);
x_22 = l_Lean_Compiler_LCNF_mkLetDecl(x_14, x_4, x_16, x_18, x_19, x_20, x_21, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_take(x_17, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = lean_unbox(x_30);
x_33 = lean_unbox(x_31);
x_34 = l_Lean_LocalContext_mkLetDecl(x_28, x_29, x_14, x_2, x_3, x_32, x_33);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_26, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_26, 4);
lean_inc(x_38);
lean_inc(x_23);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_23);
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_ctor_get(x_26, 5);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 4, x_40);
lean_ctor_set(x_42, 5, x_41);
x_43 = lean_st_ref_set(x_17, x_42, x_27);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_23);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_23);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_5, 0);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_mk_empty_array_with_capacity(x_88);
lean_inc(x_87);
x_90 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_55 = x_90;
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_10;
goto block_86;
}
else
{
lean_object* x_91; 
x_91 = lean_box(1);
x_55 = x_91;
x_56 = x_6;
x_57 = x_7;
x_58 = x_8;
x_59 = x_9;
x_60 = x_10;
goto block_86;
}
block_86:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_inc(x_53);
x_61 = l_Lean_Compiler_LCNF_mkLetDecl(x_53, x_4, x_55, x_57, x_58, x_59, x_60, x_54);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_take(x_56, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_box(0);
x_70 = lean_box(0);
x_71 = lean_unbox(x_69);
x_72 = lean_unbox(x_70);
x_73 = l_Lean_LocalContext_mkLetDecl(x_67, x_68, x_53, x_2, x_3, x_71, x_72);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_65, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 4);
lean_inc(x_77);
lean_inc(x_62);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_62);
x_79 = lean_array_push(x_77, x_78);
x_80 = lean_ctor_get(x_65, 5);
lean_inc(x_80);
lean_dec(x_65);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_74);
lean_ctor_set(x_81, 2, x_75);
lean_ctor_set(x_81, 3, x_76);
lean_ctor_set(x_81, 4, x_79);
lean_ctor_set(x_81, 5, x_80);
x_82 = lean_st_ref_set(x_56, x_81, x_66);
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
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_62);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_10, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = l_Lean_Compiler_LCNF_Param_toExpr(x_15);
x_18 = lean_array_push(x_2, x_17);
x_19 = lean_array_push(x_3, x_15);
x_1 = x_12;
x_2 = x_18;
x_3 = x_19;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
x_25 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(x_1, x_9, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_expr_instantiate_rev(x_14, x_3);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_2, x_20);
lean_dec(x_2);
lean_inc(x_18);
x_22 = l_Lean_Compiler_LCNF_Param_toExpr(x_18);
x_23 = lean_array_push(x_3, x_22);
x_24 = lean_array_push(x_4, x_18);
x_1 = x_15;
x_2 = x_21;
x_3 = x_23;
x_4 = x_24;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_30 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_33 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(x_1, x_2, x_10, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_5; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_Environment_find_x3f(x_1, x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
goto block_14;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
switch (lean_obj_tag(x_18)) {
case 4:
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
return x_20;
}
case 6:
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_1);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
return x_22;
}
case 7:
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
return x_24;
}
default: 
{
lean_dec(x_18);
goto block_14;
}
}
}
block_11:
{
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc(x_4);
x_6 = l_Lean_Environment_isProjectionFn(x_1, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("Eq", 2, 2);
x_8 = lean_mk_string_unchecked("ndrec", 5, 5);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_name_eq(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
return x_10;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
block_14:
{
uint8_t x_12; 
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Lean_isCasesOnRecursor(x_1, x_4);
if (x_12 == 0)
{
uint8_t x_13; 
lean_inc(x_4);
lean_inc(x_1);
x_13 = lean_is_no_confusion(x_1, x_4);
x_5 = x_13;
goto block_11;
}
else
{
x_5 = x_12;
goto block_11;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = l_Lean_mkAppN(x_1, x_4);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_mkLambdaFVars(x_4, x_11, x_2, x_3, x_2, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_9 = lean_st_ref_get(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_13);
lean_inc(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
lean_inc(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_13);
lean_inc(x_14);
x_20 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_7);
lean_ctor_set(x_20, 2, x_7);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_17);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set(x_20, 8, x_19);
lean_inc(x_13);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_13);
lean_inc(x_13);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_13);
lean_inc(x_13);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_13);
lean_inc(x_13);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_13);
lean_inc(x_24);
lean_inc(x_21);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_24);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_unsigned_to_nat(5u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_to_nat(x_28);
x_30 = lean_nat_pow(x_26, x_29);
lean_dec(x_29);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = lean_usize_to_nat(x_31);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_7);
lean_ctor_set(x_35, 3, x_7);
lean_ctor_set_usize(x_35, 4, x_28);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_13);
lean_inc_n(x_14, 2);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 2, x_14);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_12);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_37);
x_39 = lean_st_mk_ref(x_38, x_11);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_51 = lean_box(1);
x_52 = lean_box(1);
x_53 = lean_box(0);
x_54 = lean_box(2);
x_55 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_55, 0, x_8);
lean_ctor_set_uint8(x_55, 1, x_8);
lean_ctor_set_uint8(x_55, 2, x_8);
lean_ctor_set_uint8(x_55, 3, x_8);
lean_ctor_set_uint8(x_55, 4, x_8);
x_56 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 5, x_56);
x_57 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 6, x_57);
lean_ctor_set_uint8(x_55, 7, x_8);
x_58 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 8, x_58);
x_59 = lean_unbox(x_52);
lean_ctor_set_uint8(x_55, 9, x_59);
x_60 = lean_unbox(x_53);
lean_ctor_set_uint8(x_55, 10, x_60);
x_61 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 11, x_61);
x_62 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 12, x_62);
x_63 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 13, x_63);
x_64 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, 14, x_64);
x_65 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 15, x_65);
x_66 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 16, x_66);
x_67 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 17, x_67);
x_68 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_55);
x_69 = lean_ctor_get(x_10, 0);
lean_inc(x_69);
lean_dec(x_10);
x_70 = lean_mk_empty_array_with_capacity(x_7);
x_71 = lean_box(0);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_73, 0, x_55);
lean_ctor_set(x_73, 1, x_12);
lean_ctor_set(x_73, 2, x_69);
lean_ctor_set(x_73, 3, x_70);
lean_ctor_set(x_73, 4, x_71);
lean_ctor_set(x_73, 5, x_7);
lean_ctor_set(x_73, 6, x_72);
lean_ctor_set_uint64(x_73, sizeof(void*)*7, x_68);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 8, x_8);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 9, x_8);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 10, x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_40);
lean_inc(x_73);
lean_inc(x_1);
x_74 = lean_infer_type(x_1, x_73, x_40, x_4, x_5, x_41);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_box(x_8);
x_78 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_78, 0, x_1);
lean_closure_set(x_78, 1, x_77);
lean_closure_set(x_78, 2, x_51);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_2);
lean_inc(x_40);
x_80 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_75, x_79, x_78, x_8, x_73, x_40, x_4, x_5, x_76);
x_42 = x_80;
goto block_50;
}
else
{
lean_dec(x_73);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = x_74;
goto block_50;
}
block_50:
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_get(x_40, x_44);
lean_dec(x_40);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_dec(x_40);
return x_42;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_6);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = l_Lean_Expr_lam___override(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 6)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; size_t x_17; size_t x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
x_17 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_18 = lean_ptr_addr(x_2);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_10);
x_12 = x_19;
goto block_16;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_21 = lean_ptr_addr(x_5);
x_22 = lean_usize_dec_eq(x_20, x_21);
x_12 = x_22;
goto block_16;
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = l_Lean_Expr_lam___override(x_8, x_2, x_5, x_4);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_11, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = l_Lean_Expr_lam___override(x_8, x_2, x_5, x_4);
return x_15;
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_24 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_25 = lean_unsigned_to_nat(1848u);
x_26 = lean_unsigned_to_nat(19u);
x_27 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_28 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_23, x_24, x_25, x_26, x_27);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
x_29 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_6 = l_Lean_BinderInfo_isImplicit(x_5);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
lean_dec(x_1);
lean_inc(x_4);
x_7 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_4);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_Expr_bvar___override(x_37);
x_41 = l_Lean_Expr_app___override(x_36, x_40);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_41);
lean_dec(x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_37);
x_43 = lean_expr_has_loose_bvar(x_36, x_38);
if (x_43 == 0)
{
if (x_6 == 0)
{
lean_dec(x_36);
goto block_34;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_expr_lower_loose_bvars(x_36, x_44, x_44);
lean_dec(x_36);
return x_45;
}
}
else
{
lean_dec(x_36);
goto block_34;
}
}
}
case 1:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
x_48 = l_Lean_Expr_fvar___override(x_47);
x_49 = l_Lean_Expr_app___override(x_46, x_48);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_49);
lean_dec(x_49);
return x_50;
}
case 2:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_7, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
lean_dec(x_35);
x_53 = l_Lean_Expr_mvar___override(x_52);
x_54 = l_Lean_Expr_app___override(x_51, x_53);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_54);
lean_dec(x_54);
return x_55;
}
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_7, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_35, 0);
lean_inc(x_57);
lean_dec(x_35);
x_58 = l_Lean_Expr_sort___override(x_57);
x_59 = l_Lean_Expr_app___override(x_56, x_58);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_59);
lean_dec(x_59);
return x_60;
}
case 4:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_7, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_35, 1);
lean_inc(x_63);
lean_dec(x_35);
x_64 = l_Lean_Expr_const___override(x_62, x_63);
x_65 = l_Lean_Expr_app___override(x_61, x_64);
x_66 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_65);
lean_dec(x_65);
return x_66;
}
case 5:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_35, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_35, 1);
lean_inc(x_69);
lean_dec(x_35);
x_70 = l_Lean_Expr_app___override(x_68, x_69);
x_71 = l_Lean_Expr_app___override(x_67, x_70);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_71);
lean_dec(x_71);
return x_72;
}
case 6:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_7, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_35, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_35, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_35, 2);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_78 = l_Lean_Expr_lam___override(x_74, x_75, x_76, x_77);
x_79 = l_Lean_Expr_app___override(x_73, x_78);
x_80 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_79);
lean_dec(x_79);
return x_80;
}
case 7:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_7, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_35, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_35, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_35, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_35, sizeof(void*)*3 + 8);
lean_dec(x_35);
x_86 = l_Lean_Expr_forallE___override(x_82, x_83, x_84, x_85);
x_87 = l_Lean_Expr_app___override(x_81, x_86);
x_88 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_87);
lean_dec(x_87);
return x_88;
}
case 8:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_89 = lean_ctor_get(x_7, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_35, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_35, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_35, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_35, 3);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_35, sizeof(void*)*4 + 8);
lean_dec(x_35);
x_95 = l_Lean_Expr_letE___override(x_90, x_91, x_92, x_93, x_94);
x_96 = l_Lean_Expr_app___override(x_89, x_95);
x_97 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_96);
lean_dec(x_96);
return x_97;
}
case 9:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_7, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_35, 0);
lean_inc(x_99);
lean_dec(x_35);
x_100 = l_Lean_Expr_lit___override(x_99);
x_101 = l_Lean_Expr_app___override(x_98, x_100);
x_102 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_101);
lean_dec(x_101);
return x_102;
}
case 10:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_7, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_35, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_35, 1);
lean_inc(x_105);
lean_dec(x_35);
x_106 = l_Lean_Expr_mdata___override(x_104, x_105);
x_107 = l_Lean_Expr_app___override(x_103, x_106);
x_108 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_107);
lean_dec(x_107);
return x_108;
}
default: 
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_7, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_35, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_35, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_35, 2);
lean_inc(x_112);
lean_dec(x_35);
x_113 = l_Lean_Expr_proj___override(x_110, x_111, x_112);
x_114 = l_Lean_Expr_app___override(x_109, x_113);
x_115 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_114);
lean_dec(x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; 
lean_inc(x_7);
x_116 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_2, x_3, x_4, x_5, x_7, x_7);
lean_dec(x_7);
return x_116;
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = l_Lean_Expr_lam___override(x_8, x_3, x_7, x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_10, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = l_Lean_Expr_lam___override(x_8, x_3, x_7, x_5);
return x_14;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_9;
}
}
}
block_34:
{
lean_object* x_16; 
lean_inc(x_3);
x_16 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_16) == 6)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_16, sizeof(void*)*3 + 8);
x_21 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_22 = lean_ptr_addr(x_3);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_19);
x_8 = x_17;
x_9 = x_16;
x_10 = x_20;
x_11 = x_23;
goto block_15;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = lean_ptr_addr(x_19);
lean_dec(x_19);
x_25 = lean_ptr_addr(x_7);
x_26 = lean_usize_dec_eq(x_24, x_25);
x_8 = x_17;
x_9 = x_16;
x_10 = x_20;
x_11 = x_26;
goto block_15;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
x_27 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_28 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_29 = lean_unsigned_to_nat(1848u);
x_30 = lean_unsigned_to_nat(19u);
x_31 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_32 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_27, x_28, x_29, x_30, x_31);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
x_33 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_32);
return x_33;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit___lam__0(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_litToValue(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("_x", 2, 2);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_9, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 1)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_12);
x_15 = lean_expr_instantiate1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_1 = x_15;
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_nat_add(x_11, x_10);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_17, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_1 = x_19;
x_2 = x_17;
x_6 = x_20;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_12 = l_instMonadEIO(lean_box(0));
x_13 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
lean_inc(x_27);
lean_inc(x_24);
lean_inc(x_21);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
x_30 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_24);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_27);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
x_44 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_43);
x_45 = lean_box(0);
x_46 = l_instInhabitedOfMonad___redArg(x_44, x_45);
x_47 = lean_panic_fn(x_46, x_1);
x_48 = lean_apply_6(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
return x_48;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("runtime", 7, 7);
x_4 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_2);
x_14 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_13, x_1, x_2);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 5);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
x_20 = lean_st_ref_set(x_3, x_19, x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 4);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_2, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_11);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 7);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 8);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 9);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 10);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_29 = lean_ctor_get(x_5, 11);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_31 = lean_ctor_get(x_5, 12);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_18);
lean_ctor_set(x_32, 4, x_9);
lean_ctor_set(x_32, 5, x_22);
lean_ctor_set(x_32, 6, x_23);
lean_ctor_set(x_32, 7, x_24);
lean_ctor_set(x_32, 8, x_25);
lean_ctor_set(x_32, 9, x_26);
lean_ctor_set(x_32, 10, x_27);
lean_ctor_set(x_32, 11, x_29);
lean_ctor_set(x_32, 12, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*13, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*13 + 1, x_30);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_st_ref_get(x_2, x_14);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 5);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_40, x_33);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
if (x_10 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_33);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_42, x_2, x_3, x_4, x_32, x_6, x_36);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
else
{
lean_dec(x_33);
goto block_39;
}
}
else
{
lean_dec(x_41);
lean_dec(x_33);
goto block_39;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_37, x_2, x_3, x_4, x_32, x_6, x_36);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
}
case 4:
{
lean_object* x_44; 
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_32, x_6, x_14);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_45, x_2, x_3, x_4, x_32, x_6, x_46);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_47;
}
else
{
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_44;
}
}
case 5:
{
lean_object* x_48; 
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_32, x_6, x_14);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_49, x_2, x_3, x_4, x_32, x_6, x_50);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
else
{
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_48;
}
}
case 6:
{
lean_object* x_52; 
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_32, x_6, x_14);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_53, x_2, x_3, x_4, x_32, x_6, x_54);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
else
{
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_52;
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_mk_empty_array_with_capacity(x_56);
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_57, x_2, x_3, x_4, x_32, x_6, x_14);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_59, x_2, x_3, x_4, x_32, x_6, x_60);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_61;
}
else
{
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_58;
}
}
case 9:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_4);
lean_inc(x_3);
x_63 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_62, x_2, x_3, x_4, x_32, x_6, x_14);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_64, x_2, x_3, x_4, x_32, x_6, x_65);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_66;
}
else
{
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_63;
}
}
case 10:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_68 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_67, x_2, x_3, x_4, x_32, x_6, x_14);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_69, x_2, x_3, x_4, x_32, x_6, x_70);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_71;
}
else
{
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_68;
}
}
case 11:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_72, x_73, x_74, x_2, x_3, x_4, x_32, x_6, x_14);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_76, x_2, x_3, x_4, x_32, x_6, x_77);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_78;
}
else
{
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_75;
}
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_80 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCore", 42, 42);
x_81 = lean_unsigned_to_nat(435u);
x_82 = lean_unsigned_to_nat(57u);
x_83 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_84 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_79, x_80, x_81, x_82, x_83);
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_79);
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_85 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_84, x_2, x_3, x_4, x_32, x_6, x_14);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_86, x_2, x_3, x_4, x_32, x_6, x_87);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_88;
}
else
{
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_85;
}
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_16, 0);
lean_inc(x_89);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_89);
return x_11;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_11, 0);
x_91 = lean_ctor_get(x_11, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_11);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_92, x_1);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_8, x_94);
lean_dec(x_8);
x_96 = lean_ctor_get(x_5, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_5, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_5, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_5, 5);
lean_inc(x_99);
x_100 = lean_ctor_get(x_5, 6);
lean_inc(x_100);
x_101 = lean_ctor_get(x_5, 7);
lean_inc(x_101);
x_102 = lean_ctor_get(x_5, 8);
lean_inc(x_102);
x_103 = lean_ctor_get(x_5, 9);
lean_inc(x_103);
x_104 = lean_ctor_get(x_5, 10);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_106 = lean_ctor_get(x_5, 11);
lean_inc(x_106);
x_107 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_108 = lean_ctor_get(x_5, 12);
lean_inc(x_108);
lean_dec(x_5);
x_109 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_109, 0, x_96);
lean_ctor_set(x_109, 1, x_97);
lean_ctor_set(x_109, 2, x_98);
lean_ctor_set(x_109, 3, x_95);
lean_ctor_set(x_109, 4, x_9);
lean_ctor_set(x_109, 5, x_99);
lean_ctor_set(x_109, 6, x_100);
lean_ctor_set(x_109, 7, x_101);
lean_ctor_set(x_109, 8, x_102);
lean_ctor_set(x_109, 9, x_103);
lean_ctor_set(x_109, 10, x_104);
lean_ctor_set(x_109, 11, x_106);
lean_ctor_set(x_109, 12, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*13, x_105);
lean_ctor_set_uint8(x_109, sizeof(void*)*13 + 1, x_107);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
x_111 = lean_st_ref_get(x_2, x_91);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_117 = lean_ctor_get(x_112, 5);
lean_inc(x_117);
lean_dec(x_112);
x_118 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_117, x_110);
lean_dec(x_117);
if (lean_obj_tag(x_118) == 0)
{
if (x_10 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_110);
x_120 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_119, x_2, x_3, x_4, x_109, x_6, x_113);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_120;
}
else
{
lean_dec(x_110);
goto block_116;
}
}
else
{
lean_dec(x_118);
lean_dec(x_110);
goto block_116;
}
block_116:
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_box(0);
x_115 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_114, x_2, x_3, x_4, x_109, x_6, x_113);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_115;
}
}
case 4:
{
lean_object* x_121; 
lean_inc(x_6);
lean_inc(x_109);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_121 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_109, x_6, x_91);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_122, x_2, x_3, x_4, x_109, x_6, x_123);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_124;
}
else
{
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_121;
}
}
case 5:
{
lean_object* x_125; 
lean_inc(x_6);
lean_inc(x_109);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_125 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_109, x_6, x_91);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_126, x_2, x_3, x_4, x_109, x_6, x_127);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_128;
}
else
{
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_125;
}
}
case 6:
{
lean_object* x_129; 
lean_inc(x_6);
lean_inc(x_109);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_129 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_109, x_6, x_91);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_130, x_2, x_3, x_4, x_109, x_6, x_131);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_132;
}
else
{
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_129;
}
}
case 8:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_mk_empty_array_with_capacity(x_133);
lean_inc(x_6);
lean_inc(x_109);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_135 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_134, x_2, x_3, x_4, x_109, x_6, x_91);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_136, x_2, x_3, x_4, x_109, x_6, x_137);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_138;
}
else
{
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_135;
}
}
case 9:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
lean_inc(x_6);
lean_inc(x_109);
lean_inc(x_4);
lean_inc(x_3);
x_140 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_139, x_2, x_3, x_4, x_109, x_6, x_91);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_141, x_2, x_3, x_4, x_109, x_6, x_142);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_143;
}
else
{
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_140;
}
}
case 10:
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_1, 1);
lean_inc(x_144);
lean_inc(x_6);
lean_inc(x_109);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_145 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_144, x_2, x_3, x_4, x_109, x_6, x_91);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_146, x_2, x_3, x_4, x_109, x_6, x_147);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_148;
}
else
{
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_145;
}
}
case 11:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_1, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_1, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_1, 2);
lean_inc(x_151);
lean_inc(x_6);
lean_inc(x_109);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_152 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_149, x_150, x_151, x_2, x_3, x_4, x_109, x_6, x_91);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_153, x_2, x_3, x_4, x_109, x_6, x_154);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_155;
}
else
{
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_152;
}
}
default: 
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_157 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCore", 42, 42);
x_158 = lean_unsigned_to_nat(435u);
x_159 = lean_unsigned_to_nat(57u);
x_160 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_161 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_156, x_157, x_158, x_159, x_160);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_156);
lean_inc(x_6);
lean_inc(x_109);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_162 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_161, x_2, x_3, x_4, x_109, x_6, x_91);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_163, x_2, x_3, x_4, x_109, x_6, x_164);
lean_dec(x_6);
lean_dec(x_109);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_165;
}
else
{
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_162;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_ctor_get(x_93, 0);
lean_inc(x_166);
lean_dec(x_93);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_91);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_5, 5);
lean_inc(x_168);
lean_dec(x_5);
x_169 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_168, x_7);
return x_169;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint64_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_st_ref_get(x_3, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_18);
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
lean_inc(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_18);
lean_inc(x_18);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_18);
lean_inc(x_18);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_18);
lean_inc(x_19);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
lean_inc(x_18);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_18);
lean_inc(x_18);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_18);
lean_inc(x_18);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_18);
lean_inc(x_18);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_18);
lean_inc(x_29);
lean_inc(x_26);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_unsigned_to_nat(5u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_to_nat(x_33);
x_35 = lean_nat_pow(x_31, x_34);
lean_dec(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = lean_usize_to_nat(x_36);
x_38 = lean_mk_empty_array_with_capacity(x_37);
lean_dec(x_37);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_17);
lean_ctor_set(x_40, 3, x_17);
lean_ctor_set_usize(x_40, 4, x_33);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_18);
lean_inc_n(x_19, 2);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_19);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_25);
lean_ctor_set(x_43, 1, x_30);
lean_ctor_set(x_43, 2, x_16);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_st_mk_ref(x_43, x_15);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
x_52 = lean_box(1);
x_53 = lean_box(1);
x_54 = lean_box(0);
x_55 = lean_box(2);
x_56 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 0, 18);
x_88 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, 0, x_88);
x_89 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, 1, x_89);
x_90 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, 2, x_90);
x_91 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, 3, x_91);
x_92 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, 4, x_92);
x_93 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 5, x_93);
x_94 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 6, x_94);
x_95 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, 7, x_95);
x_96 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 8, x_96);
x_97 = lean_unbox(x_53);
lean_ctor_set_uint8(x_87, 9, x_97);
x_98 = lean_unbox(x_54);
lean_ctor_set_uint8(x_87, 10, x_98);
x_99 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 11, x_99);
x_100 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 12, x_100);
x_101 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 13, x_101);
x_102 = lean_unbox(x_55);
lean_ctor_set_uint8(x_87, 14, x_102);
x_103 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 15, x_103);
x_104 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 16, x_104);
x_105 = lean_unbox(x_52);
lean_ctor_set_uint8(x_87, 17, x_105);
x_106 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_87);
x_107 = lean_ctor_get(x_14, 0);
lean_inc(x_107);
lean_dec(x_14);
x_108 = lean_mk_empty_array_with_capacity(x_17);
x_109 = lean_box(0);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_111, 0, x_87);
lean_ctor_set(x_111, 1, x_16);
lean_ctor_set(x_111, 2, x_107);
lean_ctor_set(x_111, 3, x_108);
lean_ctor_set(x_111, 4, x_109);
lean_ctor_set(x_111, 5, x_17);
lean_ctor_set(x_111, 6, x_110);
lean_ctor_set_uint64(x_111, sizeof(void*)*7, x_106);
x_112 = lean_unbox(x_86);
lean_ctor_set_uint8(x_111, sizeof(void*)*7 + 8, x_112);
x_113 = lean_unbox(x_86);
lean_ctor_set_uint8(x_111, sizeof(void*)*7 + 9, x_113);
x_114 = lean_unbox(x_86);
lean_ctor_set_uint8(x_111, sizeof(void*)*7 + 10, x_114);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_45);
lean_inc(x_56);
x_115 = l_Lean_Meta_isProp(x_56, x_111, x_45, x_6, x_7, x_46);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_st_ref_get(x_45, x_117);
lean_dec(x_45);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_unbox(x_116);
lean_dec(x_116);
x_57 = x_120;
x_58 = x_119;
goto block_85;
}
else
{
lean_dec(x_45);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_ctor_get(x_115, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_115, 1);
lean_inc(x_122);
lean_dec(x_115);
x_123 = lean_unbox(x_121);
lean_dec(x_121);
x_57 = x_123;
x_58 = x_122;
goto block_85;
}
else
{
uint8_t x_124; 
lean_dec(x_56);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_115);
if (x_124 == 0)
{
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
block_51:
{
lean_object* x_49; 
x_49 = lean_array_push(x_2, x_47);
x_1 = x_12;
x_2 = x_49;
x_8 = x_48;
goto _start;
}
block_85:
{
if (x_57 == 0)
{
lean_object* x_59; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_56);
x_59 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_56, x_3, x_6, x_7, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_56);
x_63 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_56, x_3, x_6, x_7, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_47);
x_66 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_47, x_3, x_4, x_5, x_6, x_7, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_9, x_56, x_47, x_64, x_67, x_3, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Expr_fvar___override(x_72);
x_74 = lean_array_push(x_2, x_73);
x_1 = x_12;
x_2 = x_74;
x_8 = x_71;
goto _start;
}
else
{
lean_dec(x_64);
lean_dec(x_56);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_66;
}
}
else
{
uint8_t x_76; 
lean_dec(x_56);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_63);
if (x_76 == 0)
{
return x_63;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_63, 0);
x_78 = lean_ctor_get(x_63, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_63);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_56);
lean_dec(x_9);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
lean_dec(x_59);
x_48 = x_80;
goto block_51;
}
}
else
{
uint8_t x_81; 
lean_dec(x_56);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_59);
if (x_81 == 0)
{
return x_59;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_59, 0);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_59);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_dec(x_56);
lean_dec(x_9);
x_48 = x_58;
goto block_51;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_129 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_128, x_3, x_4, x_5, x_6, x_7, x_8);
return x_129;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_5, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 4);
lean_inc(x_69);
x_70 = lean_nat_dec_eq(x_68, x_69);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; size_t x_92; lean_object* x_93; lean_object* x_94; size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint64_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_72 = lean_st_ref_get(x_2, x_7);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_box(0);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_77);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_inc(x_77);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_77);
lean_inc(x_77);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_77);
lean_inc(x_77);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_77);
lean_inc(x_77);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_77);
lean_inc(x_77);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_77);
lean_inc(x_78);
x_84 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_76);
lean_ctor_set(x_84, 2, x_76);
lean_ctor_set(x_84, 3, x_78);
lean_ctor_set(x_84, 4, x_79);
lean_ctor_set(x_84, 5, x_80);
lean_ctor_set(x_84, 6, x_81);
lean_ctor_set(x_84, 7, x_82);
lean_ctor_set(x_84, 8, x_83);
lean_inc(x_77);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_77);
lean_inc(x_77);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_77);
lean_inc(x_77);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_77);
lean_inc(x_77);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_77);
lean_inc(x_88);
lean_inc(x_85);
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_85);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_88);
x_90 = lean_unsigned_to_nat(2u);
x_91 = lean_unsigned_to_nat(5u);
x_92 = lean_usize_of_nat(x_91);
x_93 = lean_usize_to_nat(x_92);
x_94 = lean_nat_pow(x_90, x_93);
lean_dec(x_93);
x_95 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_96 = lean_usize_to_nat(x_95);
x_97 = lean_mk_empty_array_with_capacity(x_96);
lean_dec(x_96);
lean_inc(x_97);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
lean_ctor_set(x_99, 2, x_76);
lean_ctor_set(x_99, 3, x_76);
lean_ctor_set_usize(x_99, 4, x_92);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_77);
lean_inc_n(x_78, 2);
x_101 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_101, 0, x_78);
lean_ctor_set(x_101, 1, x_78);
lean_ctor_set(x_101, 2, x_78);
lean_ctor_set(x_101, 3, x_100);
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_84);
lean_ctor_set(x_102, 1, x_89);
lean_ctor_set(x_102, 2, x_75);
lean_ctor_set(x_102, 3, x_99);
lean_ctor_set(x_102, 4, x_101);
lean_inc(x_102);
x_103 = lean_st_mk_ref(x_102, x_74);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_68, x_106);
lean_dec(x_68);
x_108 = lean_ctor_get(x_5, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_5, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_5, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_5, 5);
lean_inc(x_111);
x_112 = lean_ctor_get(x_5, 6);
lean_inc(x_112);
x_113 = lean_ctor_get(x_5, 7);
lean_inc(x_113);
x_114 = lean_ctor_get(x_5, 8);
lean_inc(x_114);
x_115 = lean_ctor_get(x_5, 9);
lean_inc(x_115);
x_116 = lean_ctor_get(x_5, 10);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_118 = lean_ctor_get(x_5, 11);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_120 = lean_ctor_get(x_5, 12);
lean_inc(x_120);
lean_dec(x_5);
x_121 = lean_box(1);
x_122 = lean_box(1);
x_123 = lean_box(0);
x_124 = lean_box(2);
x_125 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_125, 0, x_108);
lean_ctor_set(x_125, 1, x_109);
lean_ctor_set(x_125, 2, x_110);
lean_ctor_set(x_125, 3, x_107);
lean_ctor_set(x_125, 4, x_69);
lean_ctor_set(x_125, 5, x_111);
lean_ctor_set(x_125, 6, x_112);
lean_ctor_set(x_125, 7, x_113);
lean_ctor_set(x_125, 8, x_114);
lean_ctor_set(x_125, 9, x_115);
lean_ctor_set(x_125, 10, x_116);
lean_ctor_set(x_125, 11, x_118);
lean_ctor_set(x_125, 12, x_120);
lean_ctor_set_uint8(x_125, sizeof(void*)*13, x_117);
lean_ctor_set_uint8(x_125, sizeof(void*)*13 + 1, x_119);
x_126 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_126, 0, x_70);
lean_ctor_set_uint8(x_126, 1, x_70);
lean_ctor_set_uint8(x_126, 2, x_70);
lean_ctor_set_uint8(x_126, 3, x_70);
lean_ctor_set_uint8(x_126, 4, x_70);
x_127 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 5, x_127);
x_128 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 6, x_128);
lean_ctor_set_uint8(x_126, 7, x_70);
x_129 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 8, x_129);
x_130 = lean_unbox(x_122);
lean_ctor_set_uint8(x_126, 9, x_130);
x_131 = lean_unbox(x_123);
lean_ctor_set_uint8(x_126, 10, x_131);
x_132 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 11, x_132);
x_133 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 12, x_133);
x_134 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 13, x_134);
x_135 = lean_unbox(x_124);
lean_ctor_set_uint8(x_126, 14, x_135);
x_136 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 15, x_136);
x_137 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 16, x_137);
x_138 = lean_unbox(x_121);
lean_ctor_set_uint8(x_126, 17, x_138);
x_139 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_126);
x_140 = lean_ctor_get(x_73, 0);
lean_inc(x_140);
lean_dec(x_73);
x_141 = lean_mk_empty_array_with_capacity(x_76);
x_142 = lean_box(0);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_144, 0, x_126);
lean_ctor_set(x_144, 1, x_75);
lean_ctor_set(x_144, 2, x_140);
lean_ctor_set(x_144, 3, x_141);
lean_ctor_set(x_144, 4, x_142);
lean_ctor_set(x_144, 5, x_76);
lean_ctor_set(x_144, 6, x_143);
lean_ctor_set_uint64(x_144, sizeof(void*)*7, x_139);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 8, x_70);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 9, x_70);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 10, x_70);
lean_inc(x_6);
lean_inc(x_125);
lean_inc(x_104);
lean_inc(x_1);
x_145 = lean_infer_type(x_1, x_144, x_104, x_125, x_6, x_105);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_st_ref_get(x_104, x_147);
lean_dec(x_104);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_unbox(x_123);
x_151 = lean_unbox(x_122);
x_152 = lean_unbox(x_124);
x_153 = lean_unbox(x_121);
x_30 = x_150;
x_31 = x_102;
x_32 = x_76;
x_33 = x_125;
x_34 = x_151;
x_35 = x_152;
x_36 = x_70;
x_37 = x_153;
x_38 = x_75;
x_39 = x_146;
x_40 = x_149;
goto block_67;
}
else
{
lean_dec(x_104);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; 
x_154 = lean_ctor_get(x_145, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_145, 1);
lean_inc(x_155);
lean_dec(x_145);
x_156 = lean_unbox(x_123);
x_157 = lean_unbox(x_122);
x_158 = lean_unbox(x_124);
x_159 = lean_unbox(x_121);
x_30 = x_156;
x_31 = x_102;
x_32 = x_76;
x_33 = x_125;
x_34 = x_157;
x_35 = x_158;
x_36 = x_70;
x_37 = x_159;
x_38 = x_75;
x_39 = x_154;
x_40 = x_155;
goto block_67;
}
else
{
uint8_t x_160; 
lean_dec(x_125);
lean_dec(x_102);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_145);
if (x_160 == 0)
{
return x_145;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_145, 0);
x_162 = lean_ctor_get(x_145, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_145);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_7);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_ctor_get(x_5, 5);
lean_inc(x_166);
lean_dec(x_5);
x_167 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_166, x_7);
return x_167;
}
block_29:
{
if (x_10 == 0)
{
lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_8);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_9, x_2, x_8, x_6, x_11);
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
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_8, x_6, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
}
block_67:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_st_ref_get(x_2, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_mk_ref(x_31, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_47, 0, x_36);
lean_ctor_set_uint8(x_47, 1, x_36);
lean_ctor_set_uint8(x_47, 2, x_36);
lean_ctor_set_uint8(x_47, 3, x_36);
lean_ctor_set_uint8(x_47, 4, x_36);
lean_ctor_set_uint8(x_47, 5, x_37);
lean_ctor_set_uint8(x_47, 6, x_37);
lean_ctor_set_uint8(x_47, 7, x_36);
lean_ctor_set_uint8(x_47, 8, x_37);
lean_ctor_set_uint8(x_47, 9, x_34);
lean_ctor_set_uint8(x_47, 10, x_30);
lean_ctor_set_uint8(x_47, 11, x_37);
lean_ctor_set_uint8(x_47, 12, x_37);
lean_ctor_set_uint8(x_47, 13, x_37);
lean_ctor_set_uint8(x_47, 14, x_35);
lean_ctor_set_uint8(x_47, 15, x_37);
lean_ctor_set_uint8(x_47, 16, x_37);
lean_ctor_set_uint8(x_47, 17, x_37);
x_48 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_47);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_mk_empty_array_with_capacity(x_32);
x_51 = lean_box(0);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set(x_53, 5, x_32);
lean_ctor_set(x_53, 6, x_52);
lean_ctor_set_uint64(x_53, sizeof(void*)*7, x_48);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 8, x_36);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 9, x_36);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 10, x_36);
lean_inc(x_6);
lean_inc(x_33);
lean_inc(x_45);
lean_inc(x_39);
x_54 = l_Lean_Meta_isProp(x_39, x_53, x_45, x_33, x_6, x_46);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_get(x_45, x_56);
lean_dec(x_45);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_unbox(x_55);
lean_dec(x_55);
x_8 = x_33;
x_9 = x_39;
x_10 = x_59;
x_11 = x_58;
goto block_29;
}
else
{
lean_dec(x_45);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_unbox(x_60);
lean_dec(x_60);
x_8 = x_33;
x_9 = x_39;
x_10 = x_62;
x_11 = x_61;
goto block_29;
}
else
{
uint8_t x_63; 
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
return x_54;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_ctor_get(x_54, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_54);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_12, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_14, x_2, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("_f", 2, 2);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_11, x_17, x_20, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_30; uint8_t x_31; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_1);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_1);
x_31 = l_Lean_Expr_isLambda(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
lean_dec(x_9);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(x_32, x_30);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_11);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_30, x_2, x_3, x_4, x_5, x_6, x_10);
return x_34;
}
else
{
lean_dec(x_30);
goto block_29;
}
}
else
{
lean_dec(x_30);
lean_dec(x_9);
goto block_29;
}
block_29:
{
lean_object* x_12; 
lean_inc(x_2);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_10);
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
x_16 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_15, x_2, x_14);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("_x", 2, 2);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_4);
return x_17;
}
default: 
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_3, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_17, x_2, x_14);
x_2 = x_20;
x_3 = x_21;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_set(x_2, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_1 = x_10;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
case 1:
{
lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_size(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_20, x_22, x_2, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_mk_string_unchecked("_x", 2, 2);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_26, x_28, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_4);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
default: 
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_16, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_16, 0, x_36);
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_set(x_2, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
x_15 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1_spec__1(x_10, x_12, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
case 1:
{
lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_size(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_20, x_22, x_2, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_mk_string_unchecked("_x", 2, 2);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_26, x_28, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_4);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
default: 
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_16, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_16, 0, x_36);
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_get_projection_info(x_7, x_1);
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
x_12 = lean_get_projection_info(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___redArg(x_1, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_set(x_2, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_1 = x_10;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_set(x_3, x_4, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_4, x_14);
lean_dec(x_4);
x_2 = x_11;
x_3 = x_13;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_4);
x_17 = lean_apply_8(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
x_10 = l_Lean_Expr_sort___override(x_9);
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
x_15 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1(x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Expr_letFunAppArgs_x3f(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Expr_getAppFn(x_1);
x_20 = lean_csimp_replace_constants(x_18, x_19);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_bvar___override(x_21);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_22);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Expr_fvar___override(x_24);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_25, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_25);
return x_26;
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lean_Expr_mvar___override(x_27);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_28, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_28);
return x_29;
}
case 3:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_Expr_sort___override(x_30);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_31);
return x_32;
}
case 4:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_mk_string_unchecked("Quot", 4, 4);
x_35 = lean_mk_string_unchecked("lift", 4, 4);
lean_inc(x_34);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = lean_name_eq(x_33, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_mk_string_unchecked("mk", 2, 2);
x_39 = l_Lean_Name_mkStr2(x_34, x_38);
x_40 = lean_name_eq(x_33, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_mk_string_unchecked("Eq", 2, 2);
x_42 = lean_mk_string_unchecked("casesOn", 7, 7);
lean_inc(x_42);
lean_inc(x_41);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = lean_name_eq(x_33, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_mk_string_unchecked("rec", 3, 3);
lean_inc(x_45);
lean_inc(x_41);
x_46 = l_Lean_Name_mkStr2(x_41, x_45);
x_47 = lean_name_eq(x_33, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_mk_string_unchecked("ndrec", 5, 5);
lean_inc(x_48);
x_49 = l_Lean_Name_mkStr2(x_41, x_48);
x_50 = lean_name_eq(x_33, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_mk_string_unchecked("HEq", 3, 3);
lean_inc(x_42);
lean_inc(x_51);
x_52 = l_Lean_Name_mkStr2(x_51, x_42);
x_53 = lean_name_eq(x_33, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
lean_inc(x_45);
lean_inc(x_51);
x_54 = l_Lean_Name_mkStr2(x_51, x_45);
x_55 = lean_name_eq(x_33, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Name_mkStr2(x_51, x_48);
x_57 = lean_name_eq(x_33, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_mk_string_unchecked("And", 3, 3);
lean_inc(x_45);
lean_inc(x_58);
x_59 = l_Lean_Name_mkStr2(x_58, x_45);
x_60 = lean_name_eq(x_33, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_mk_string_unchecked("Iff", 3, 3);
lean_inc(x_45);
lean_inc(x_61);
x_62 = l_Lean_Name_mkStr2(x_61, x_45);
x_63 = lean_name_eq(x_33, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_inc(x_42);
x_64 = l_Lean_Name_mkStr2(x_58, x_42);
x_65 = lean_name_eq(x_33, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
lean_inc(x_42);
x_66 = l_Lean_Name_mkStr2(x_61, x_42);
x_67 = lean_name_eq(x_33, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_mk_string_unchecked("False", 5, 5);
lean_inc(x_45);
lean_inc(x_68);
x_69 = l_Lean_Name_mkStr2(x_68, x_45);
x_70 = lean_name_eq(x_33, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_mk_string_unchecked("Empty", 5, 5);
lean_inc(x_71);
x_72 = l_Lean_Name_mkStr2(x_71, x_45);
x_73 = lean_name_eq(x_33, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_inc(x_42);
x_74 = l_Lean_Name_mkStr2(x_68, x_42);
x_75 = lean_name_eq(x_33, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = l_Lean_Name_mkStr2(x_71, x_42);
x_77 = lean_name_eq(x_33, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_33);
x_78 = l_Lean_Compiler_LCNF_getCasesInfo_x3f(x_33, x_5, x_6, x_11);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_33);
x_81 = l_Lean_Compiler_LCNF_getCtorArity_x3f(x_33, x_5, x_6, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_get(x_6, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__1(x_85, x_5, x_6, x_86);
lean_dec(x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_33);
x_90 = lean_is_no_confusion(x_88, x_33);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___redArg(x_33, x_6, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_box(0);
x_95 = l_Lean_Expr_sort___override(x_94);
x_96 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_96);
x_97 = lean_mk_array(x_96, x_95);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_96, x_98);
lean_dec(x_96);
x_100 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__4(x_1, x_97, x_99, x_2, x_3, x_4, x_5, x_6, x_93);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_dec(x_91);
x_102 = lean_ctor_get(x_92, 0);
lean_inc(x_102);
lean_dec(x_92);
x_103 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_102, x_1, x_2, x_3, x_4, x_5, x_6, x_101);
lean_dec(x_102);
return x_103;
}
}
else
{
lean_object* x_104; 
lean_dec(x_33);
x_104 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(x_1, x_2, x_3, x_4, x_5, x_6, x_89);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_33);
x_105 = lean_ctor_get(x_81, 1);
lean_inc(x_105);
lean_dec(x_81);
x_106 = lean_ctor_get(x_82, 0);
lean_inc(x_106);
lean_dec(x_82);
x_107 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_106, x_1, x_2, x_3, x_4, x_5, x_6, x_105);
lean_dec(x_106);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_81);
if (x_108 == 0)
{
return x_81;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_81, 0);
x_110 = lean_ctor_get(x_81, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_81);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_78, 1);
lean_inc(x_112);
lean_dec(x_78);
x_113 = lean_ctor_get(x_79, 0);
lean_inc(x_113);
lean_dec(x_79);
x_114 = lean_st_ref_get(x_6, x_112);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__1(x_115, x_5, x_6, x_116);
lean_dec(x_115);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_get_implemented_by(x_118, x_33);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(x_113, x_1, x_2, x_3, x_4, x_5, x_6, x_119);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_120);
x_122 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy), 9, 1);
lean_closure_set(x_122, 0, x_113);
x_123 = lean_box(0);
x_124 = l_Lean_Expr_sort___override(x_123);
x_125 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_125);
x_126 = lean_mk_array(x_125, x_124);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_sub(x_125, x_127);
lean_dec(x_125);
x_129 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__5(x_122, x_1, x_126, x_128, x_2, x_3, x_4, x_5, x_6, x_119);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_78);
if (x_130 == 0)
{
return x_78;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_78, 0);
x_132 = lean_ctor_get(x_78, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_78);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; 
lean_dec(x_33);
x_134 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_134;
}
}
else
{
lean_object* x_135; 
lean_dec(x_71);
lean_dec(x_42);
lean_dec(x_33);
x_135 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_135;
}
}
else
{
lean_object* x_136; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_42);
lean_dec(x_33);
x_136 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_136;
}
}
else
{
lean_object* x_137; 
lean_dec(x_68);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
x_137 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_137;
}
}
else
{
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
goto block_14;
}
}
else
{
lean_dec(x_61);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
goto block_14;
}
}
else
{
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
goto block_17;
}
}
else
{
lean_dec(x_58);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
goto block_17;
}
}
else
{
lean_object* x_138; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_138;
}
}
else
{
lean_object* x_139; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
x_139 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_139;
}
}
else
{
lean_object* x_140; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
x_140 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_140;
}
}
else
{
lean_object* x_141; 
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_33);
x_141 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_141;
}
}
else
{
lean_object* x_142; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_33);
x_142 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_142;
}
}
else
{
lean_object* x_143; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_33);
x_143 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_33);
x_144 = lean_unsigned_to_nat(3u);
x_145 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_144, x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_145;
}
}
else
{
lean_object* x_146; 
lean_dec(x_34);
lean_dec(x_33);
x_146 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_146;
}
}
case 5:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_20, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_20, 1);
lean_inc(x_148);
lean_dec(x_20);
x_149 = l_Lean_Expr_app___override(x_147, x_148);
x_150 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_149, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_149);
return x_150;
}
case 6:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_20, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_20, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_20, 2);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 8);
lean_dec(x_20);
x_155 = l_Lean_Expr_lam___override(x_151, x_152, x_153, x_154);
x_156 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_155, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_155);
return x_156;
}
case 7:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_20, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_20, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_20, 2);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 8);
lean_dec(x_20);
x_161 = l_Lean_Expr_forallE___override(x_157, x_158, x_159, x_160);
x_162 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_161, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_161);
return x_162;
}
case 8:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_20, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_20, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_20, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_20, 3);
lean_inc(x_166);
x_167 = lean_ctor_get_uint8(x_20, sizeof(void*)*4 + 8);
lean_dec(x_20);
x_168 = l_Lean_Expr_letE___override(x_163, x_164, x_165, x_166, x_167);
x_169 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_168, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_168);
return x_169;
}
case 9:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_20, 0);
lean_inc(x_170);
lean_dec(x_20);
x_171 = l_Lean_Expr_lit___override(x_170);
x_172 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_171, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_171);
return x_172;
}
case 10:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_20, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_20, 1);
lean_inc(x_174);
lean_dec(x_20);
x_175 = l_Lean_Expr_mdata___override(x_173, x_174);
x_176 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_175, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_175);
return x_176;
}
default: 
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_20, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_20, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_20, 2);
lean_inc(x_179);
lean_dec(x_20);
x_180 = l_Lean_Expr_proj___override(x_177, x_178, x_179);
x_181 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_180, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_180);
return x_181;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_11);
return x_13;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_11);
return x_16;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_1);
x_182 = lean_ctor_get(x_8, 0);
lean_inc(x_182);
lean_dec(x_8);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
lean_dec(x_182);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
lean_dec(x_184);
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
lean_dec(x_185);
x_191 = lean_box(1);
x_192 = lean_unbox(x_191);
x_193 = l_Lean_Expr_letE___override(x_187, x_188, x_189, x_190, x_192);
x_194 = l_Lean_mkAppN(x_193, x_186);
lean_dec(x_186);
x_195 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_194, x_2, x_3, x_4, x_5, x_6, x_7);
return x_195;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_61 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; size_t x_155; lean_object* x_156; lean_object* x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint64_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_135 = lean_st_ref_get(x_2, x_7);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_box(0);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_140);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
lean_inc(x_140);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_140);
lean_inc(x_140);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_140);
lean_inc(x_140);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_140);
lean_inc(x_140);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_140);
lean_inc(x_140);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_140);
lean_inc(x_141);
x_147 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_147, 0, x_139);
lean_ctor_set(x_147, 1, x_139);
lean_ctor_set(x_147, 2, x_139);
lean_ctor_set(x_147, 3, x_141);
lean_ctor_set(x_147, 4, x_142);
lean_ctor_set(x_147, 5, x_143);
lean_ctor_set(x_147, 6, x_144);
lean_ctor_set(x_147, 7, x_145);
lean_ctor_set(x_147, 8, x_146);
lean_inc(x_140);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_140);
lean_inc(x_140);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_140);
lean_inc(x_140);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_140);
lean_inc(x_140);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_140);
lean_inc(x_151);
lean_inc(x_148);
x_152 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_149);
lean_ctor_set(x_152, 2, x_150);
lean_ctor_set(x_152, 3, x_148);
lean_ctor_set(x_152, 4, x_151);
lean_ctor_set(x_152, 5, x_151);
x_153 = lean_unsigned_to_nat(2u);
x_154 = lean_unsigned_to_nat(5u);
x_155 = lean_usize_of_nat(x_154);
x_156 = lean_usize_to_nat(x_155);
x_157 = lean_nat_pow(x_153, x_156);
lean_dec(x_156);
x_158 = lean_usize_of_nat(x_157);
lean_dec(x_157);
x_159 = lean_usize_to_nat(x_158);
x_160 = lean_mk_empty_array_with_capacity(x_159);
lean_dec(x_159);
lean_inc(x_160);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
lean_ctor_set(x_162, 2, x_139);
lean_ctor_set(x_162, 3, x_139);
lean_ctor_set_usize(x_162, 4, x_155);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_140);
lean_inc_n(x_141, 2);
x_164 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_164, 0, x_141);
lean_ctor_set(x_164, 1, x_141);
lean_ctor_set(x_164, 2, x_141);
lean_ctor_set(x_164, 3, x_163);
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_147);
lean_ctor_set(x_165, 1, x_152);
lean_ctor_set(x_165, 2, x_138);
lean_ctor_set(x_165, 3, x_162);
lean_ctor_set(x_165, 4, x_164);
x_166 = lean_st_mk_ref(x_165, x_137);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_box(1);
x_170 = lean_box(1);
x_171 = lean_box(0);
x_172 = lean_box(2);
x_173 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_173, 0, x_61);
lean_ctor_set_uint8(x_173, 1, x_61);
lean_ctor_set_uint8(x_173, 2, x_61);
lean_ctor_set_uint8(x_173, 3, x_61);
lean_ctor_set_uint8(x_173, 4, x_61);
x_174 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 5, x_174);
x_175 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 6, x_175);
lean_ctor_set_uint8(x_173, 7, x_61);
x_176 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 8, x_176);
x_177 = lean_unbox(x_170);
lean_ctor_set_uint8(x_173, 9, x_177);
x_178 = lean_unbox(x_171);
lean_ctor_set_uint8(x_173, 10, x_178);
x_179 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 11, x_179);
x_180 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 12, x_180);
x_181 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 13, x_181);
x_182 = lean_unbox(x_172);
lean_ctor_set_uint8(x_173, 14, x_182);
x_183 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 15, x_183);
x_184 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 16, x_184);
x_185 = lean_unbox(x_169);
lean_ctor_set_uint8(x_173, 17, x_185);
x_186 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_173);
x_187 = lean_ctor_get(x_136, 0);
lean_inc(x_187);
lean_dec(x_136);
x_188 = lean_mk_empty_array_with_capacity(x_139);
x_189 = lean_box(0);
x_190 = lean_box(0);
x_191 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_191, 0, x_173);
lean_ctor_set(x_191, 1, x_138);
lean_ctor_set(x_191, 2, x_187);
lean_ctor_set(x_191, 3, x_188);
lean_ctor_set(x_191, 4, x_189);
lean_ctor_set(x_191, 5, x_139);
lean_ctor_set(x_191, 6, x_190);
lean_ctor_set_uint64(x_191, sizeof(void*)*7, x_186);
lean_ctor_set_uint8(x_191, sizeof(void*)*7 + 8, x_61);
lean_ctor_set_uint8(x_191, sizeof(void*)*7 + 9, x_61);
lean_ctor_set_uint8(x_191, sizeof(void*)*7 + 10, x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_167);
lean_inc(x_1);
x_192 = lean_infer_type(x_1, x_191, x_167, x_5, x_6, x_168);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_get(x_167, x_194);
lean_dec(x_167);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_62 = x_193;
x_63 = x_196;
goto block_134;
}
else
{
lean_dec(x_167);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
lean_dec(x_192);
x_62 = x_197;
x_63 = x_198;
goto block_134;
}
else
{
uint8_t x_199; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_192);
if (x_199 == 0)
{
return x_192;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_192, 0);
x_201 = lean_ctor_get(x_192, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_7);
return x_204;
}
block_60:
{
if (x_9 == 0)
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_8);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_8, x_2, x_5, x_6, x_10);
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
lean_dec(x_8);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_5, x_6, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_8, x_2, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Compiler_LCNF_isPredicateType(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_17);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_20);
lean_dec(x_2);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
lean_ctor_set(x_17, 0, x_34);
return x_17;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = l_Lean_Compiler_LCNF_isPredicateType(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_36);
lean_dec(x_2);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_36);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_11;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_10);
return x_59;
}
}
block_134:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; lean_object* x_85; lean_object* x_86; size_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint64_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_64 = lean_st_ref_get(x_2, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_69);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_inc(x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_69);
lean_inc(x_69);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_69);
lean_inc(x_69);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_69);
lean_inc(x_69);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_69);
lean_inc(x_69);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_69);
lean_inc(x_70);
x_76 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_68);
lean_ctor_set(x_76, 2, x_68);
lean_ctor_set(x_76, 3, x_70);
lean_ctor_set(x_76, 4, x_71);
lean_ctor_set(x_76, 5, x_72);
lean_ctor_set(x_76, 6, x_73);
lean_ctor_set(x_76, 7, x_74);
lean_ctor_set(x_76, 8, x_75);
lean_inc(x_69);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_69);
lean_inc(x_69);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_69);
lean_inc(x_69);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_69);
lean_inc(x_69);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_69);
lean_inc(x_80);
lean_inc(x_77);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_81, 2, x_79);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_80);
lean_ctor_set(x_81, 5, x_80);
x_82 = lean_unsigned_to_nat(2u);
x_83 = lean_unsigned_to_nat(5u);
x_84 = lean_usize_of_nat(x_83);
x_85 = lean_usize_to_nat(x_84);
x_86 = lean_nat_pow(x_82, x_85);
lean_dec(x_85);
x_87 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_88 = lean_usize_to_nat(x_87);
x_89 = lean_mk_empty_array_with_capacity(x_88);
lean_dec(x_88);
lean_inc(x_89);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_68);
lean_ctor_set(x_91, 3, x_68);
lean_ctor_set_usize(x_91, 4, x_84);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_69);
lean_inc_n(x_70, 2);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_70);
lean_ctor_set(x_93, 1, x_70);
lean_ctor_set(x_93, 2, x_70);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_76);
lean_ctor_set(x_94, 1, x_81);
lean_ctor_set(x_94, 2, x_67);
lean_ctor_set(x_94, 3, x_91);
lean_ctor_set(x_94, 4, x_93);
x_95 = lean_st_mk_ref(x_94, x_66);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_box(1);
x_99 = lean_box(1);
x_100 = lean_box(0);
x_101 = lean_box(2);
x_102 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_102, 0, x_61);
lean_ctor_set_uint8(x_102, 1, x_61);
lean_ctor_set_uint8(x_102, 2, x_61);
lean_ctor_set_uint8(x_102, 3, x_61);
lean_ctor_set_uint8(x_102, 4, x_61);
x_103 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 5, x_103);
x_104 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 6, x_104);
lean_ctor_set_uint8(x_102, 7, x_61);
x_105 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 8, x_105);
x_106 = lean_unbox(x_99);
lean_ctor_set_uint8(x_102, 9, x_106);
x_107 = lean_unbox(x_100);
lean_ctor_set_uint8(x_102, 10, x_107);
x_108 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 11, x_108);
x_109 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 12, x_109);
x_110 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 13, x_110);
x_111 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, 14, x_111);
x_112 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 15, x_112);
x_113 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 16, x_113);
x_114 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, 17, x_114);
x_115 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_102);
x_116 = lean_ctor_get(x_65, 0);
lean_inc(x_116);
lean_dec(x_65);
x_117 = lean_mk_empty_array_with_capacity(x_68);
x_118 = lean_box(0);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_120, 0, x_102);
lean_ctor_set(x_120, 1, x_67);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set(x_120, 4, x_118);
lean_ctor_set(x_120, 5, x_68);
lean_ctor_set(x_120, 6, x_119);
lean_ctor_set_uint64(x_120, sizeof(void*)*7, x_115);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 8, x_61);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 9, x_61);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 10, x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_96);
lean_inc(x_62);
x_121 = l_Lean_Meta_isProp(x_62, x_120, x_96, x_5, x_6, x_97);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_st_ref_get(x_96, x_123);
lean_dec(x_96);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_unbox(x_122);
lean_dec(x_122);
x_8 = x_62;
x_9 = x_126;
x_10 = x_125;
goto block_60;
}
else
{
lean_dec(x_96);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
lean_dec(x_121);
x_129 = lean_unbox(x_127);
lean_dec(x_127);
x_8 = x_62;
x_9 = x_129;
x_10 = x_128;
goto block_60;
}
else
{
uint8_t x_130; 
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_121);
if (x_130 == 0)
{
return x_121;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_121, 0);
x_132 = lean_ctor_get(x_121, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_121);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_9 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitAppDefaultConst", 53, 53);
x_10 = lean_unsigned_to_nat(477u);
x_11 = lean_unsigned_to_nat(68u);
x_12 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_csimp_replace_constants(x_12, x_1);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_bvar___override(x_14);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_15, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_15);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_Expr_fvar___override(x_17);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_18, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_18);
return x_19;
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = l_Lean_Expr_mvar___override(x_20);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_21, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l_Lean_Expr_sort___override(x_23);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_24, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_24);
return x_25;
}
case 4:
{
lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; size_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_array_size(x_2);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_usize_of_nat(x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_28, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_32);
x_35 = lean_mk_string_unchecked("_x", 2, 2);
x_36 = l_Lean_Name_mkStr1(x_35);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_34, x_36, x_3, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_3);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
case 5:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_42 = lean_ctor_get(x_13, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_dec(x_13);
x_44 = l_Lean_Expr_app___override(x_42, x_43);
x_45 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_44, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_44);
return x_45;
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_13, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_13, sizeof(void*)*3 + 8);
lean_dec(x_13);
x_50 = l_Lean_Expr_lam___override(x_46, x_47, x_48, x_49);
x_51 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_50, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_50);
return x_51;
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
x_52 = lean_ctor_get(x_13, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_13, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_13, sizeof(void*)*3 + 8);
lean_dec(x_13);
x_56 = l_Lean_Expr_forallE___override(x_52, x_53, x_54, x_55);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_56, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_56);
return x_57;
}
case 8:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
x_58 = lean_ctor_get(x_13, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_13, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_13, 3);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_13, sizeof(void*)*4 + 8);
lean_dec(x_13);
x_63 = l_Lean_Expr_letE___override(x_58, x_59, x_60, x_61, x_62);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_63, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_63);
return x_64;
}
case 9:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
x_65 = lean_ctor_get(x_13, 0);
lean_inc(x_65);
lean_dec(x_13);
x_66 = l_Lean_Expr_lit___override(x_65);
x_67 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_66, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_66);
return x_67;
}
case 10:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_2);
x_68 = lean_ctor_get(x_13, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_13, 1);
lean_inc(x_69);
lean_dec(x_13);
x_70 = l_Lean_Expr_mdata___override(x_68, x_69);
x_71 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_70, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_70);
return x_71;
}
default: 
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_2);
x_72 = lean_ctor_get(x_13, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_13, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_13, 2);
lean_inc(x_74);
lean_dec(x_13);
x_75 = l_Lean_Expr_proj___override(x_72, x_73, x_74);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_75, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_3, 2);
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
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_17);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_27);
lean_inc(x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_ctor_get(x_3, 5);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
lean_inc(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
lean_inc(x_37);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_37);
lean_inc(x_37);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_37);
x_44 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
lean_ctor_set(x_44, 7, x_42);
lean_ctor_set(x_44, 8, x_43);
lean_inc(x_35);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_45);
lean_inc(x_31);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_6);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_30);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_6);
x_50 = lean_st_ref_get(x_2, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_3, 5);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec(x_51);
x_57 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_56);
lean_dec(x_56);
x_58 = lean_ctor_get(x_3, 2);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_inc(x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_60);
lean_inc(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
lean_inc(x_60);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_60);
lean_inc(x_60);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_60);
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_61);
lean_ctor_set(x_67, 4, x_62);
lean_ctor_set(x_67, 5, x_63);
lean_ctor_set(x_67, 6, x_64);
lean_ctor_set(x_67, 7, x_65);
lean_ctor_set(x_67, 8, x_66);
lean_inc(x_58);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_57);
lean_ctor_set(x_68, 3, x_58);
x_69 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_1);
lean_inc(x_54);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_53)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_53;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_52);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_1);
x_15 = l_Lean_Environment_find_x3f(x_12, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_8);
x_16 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_unbox(x_13);
x_19 = l_Lean_MessageData_ofConstName(x_1, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("'", 1, 1);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_23, x_4, x_5, x_6, x_11);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
lean_inc(x_1);
x_31 = l_Lean_Environment_find_x3f(x_28, x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_unbox(x_29);
x_35 = l_Lean_MessageData_ofConstName(x_1, x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("'", 1, 1);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_39, x_4, x_5, x_6, x_27);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_9 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitProjFn", 44, 44);
x_10 = lean_unsigned_to_nat(694u);
x_11 = lean_unsigned_to_nat(45u);
x_12 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_Name_getPrefix(x_9);
x_11 = l_Lean_Compiler_LCNF_isRuntimeBultinType(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn(x_2);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Expr_bvar___override(x_13);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_Expr_fvar___override(x_16);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_17, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_17);
return x_18;
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l_Lean_Expr_mvar___override(x_19);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_20, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_20);
return x_21;
}
case 3:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = l_Lean_Expr_sort___override(x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_23, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_23);
return x_24;
}
case 4:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_25, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Core_instantiateValueLevelParams(x_28, x_26, x_6, x_7, x_29);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_sort___override(x_33);
x_35 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_35);
x_36 = lean_mk_array(x_35, x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_35, x_37);
lean_dec(x_35);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_36, x_38);
x_40 = l_Lean_Expr_beta(x_31, x_39);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_40, x_3, x_4, x_5, x_6, x_7, x_32);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 5:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
x_50 = lean_ctor_get(x_12, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_dec(x_12);
x_52 = l_Lean_Expr_app___override(x_50, x_51);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_52, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_52);
return x_53;
}
case 6:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
x_54 = lean_ctor_get(x_12, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_12, 2);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 8);
lean_dec(x_12);
x_58 = l_Lean_Expr_lam___override(x_54, x_55, x_56, x_57);
x_59 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_58, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_58);
return x_59;
}
case 7:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_60 = lean_ctor_get(x_12, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_12, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_12, 2);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 8);
lean_dec(x_12);
x_64 = l_Lean_Expr_forallE___override(x_60, x_61, x_62, x_63);
x_65 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_64, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_64);
return x_65;
}
case 8:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_2);
x_66 = lean_ctor_get(x_12, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_12, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_12, 3);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_12, sizeof(void*)*4 + 8);
lean_dec(x_12);
x_71 = l_Lean_Expr_letE___override(x_66, x_67, x_68, x_69, x_70);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_71, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_71);
return x_72;
}
case 9:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_2);
x_73 = lean_ctor_get(x_12, 0);
lean_inc(x_73);
lean_dec(x_12);
x_74 = l_Lean_Expr_lit___override(x_73);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_74, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_74);
return x_75;
}
case 10:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_2);
x_76 = lean_ctor_get(x_12, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_12, 1);
lean_inc(x_77);
lean_dec(x_12);
x_78 = l_Lean_Expr_mdata___override(x_76, x_77);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_78, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_78);
return x_79;
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_2);
x_80 = lean_ctor_get(x_12, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_12, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_12, 2);
lean_inc(x_82);
lean_dec(x_12);
x_83 = l_Lean_Expr_proj___override(x_80, x_81, x_82);
x_84 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_83, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = l_Lean_Expr_getAppNumArgs(x_2);
x_86 = lean_ctor_get(x_1, 1);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_86, x_87);
x_89 = lean_nat_dec_lt(x_85, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
x_90 = l_Lean_Expr_getAppFn(x_2);
x_91 = lean_box(0);
x_92 = l_Lean_Expr_sort___override(x_91);
lean_inc(x_85);
x_93 = lean_mk_array(x_85, x_92);
x_94 = lean_nat_sub(x_85, x_87);
lean_dec(x_85);
x_95 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_93, x_94);
x_96 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_90, x_95, x_3, x_4, x_5, x_6, x_7, x_8);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_nat_sub(x_88, x_85);
lean_dec(x_85);
lean_dec(x_88);
lean_inc(x_7);
lean_inc(x_6);
x_98 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_2, x_97, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_99, x_3, x_4, x_5, x_6, x_7, x_100);
return x_101;
}
else
{
uint8_t x_102; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_98);
if (x_102 == 0)
{
return x_98;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_98, 0);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_98);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_3);
x_15 = l_Array_toSubarray___redArg(x_3, x_4, x_14);
x_16 = l_Array_ofSubarray___redArg(x_15);
lean_dec(x_15);
x_17 = l_Lean_mkAppN(x_12, x_16);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_17, x_5, x_6, x_7, x_8, x_9, x_13);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_26; lean_object* x_27; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_153; lean_object* x_154; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; size_t x_254; lean_object* x_255; lean_object* x_256; size_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; uint8_t x_285; uint8_t x_286; uint8_t x_287; uint8_t x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; uint64_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; uint8_t x_301; uint8_t x_302; lean_object* x_303; 
x_235 = lean_st_ref_get(x_10, x_15);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_box(0);
x_239 = lean_unsigned_to_nat(0u);
x_240 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_240);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_240);
lean_inc(x_240);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_240);
lean_inc(x_240);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_240);
lean_inc(x_240);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_240);
lean_inc(x_240);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_240);
lean_inc(x_240);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_240);
lean_inc(x_241);
x_247 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_247, 0, x_239);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_239);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set(x_247, 4, x_242);
lean_ctor_set(x_247, 5, x_243);
lean_ctor_set(x_247, 6, x_244);
lean_ctor_set(x_247, 7, x_245);
lean_ctor_set(x_247, 8, x_246);
lean_inc(x_240);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_240);
lean_inc(x_240);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_240);
lean_inc(x_240);
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_240);
lean_inc(x_240);
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_240);
lean_inc(x_251);
lean_inc(x_248);
x_252 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_252, 0, x_248);
lean_ctor_set(x_252, 1, x_249);
lean_ctor_set(x_252, 2, x_250);
lean_ctor_set(x_252, 3, x_248);
lean_ctor_set(x_252, 4, x_251);
lean_ctor_set(x_252, 5, x_251);
x_253 = lean_unsigned_to_nat(5u);
x_254 = lean_usize_of_nat(x_253);
x_255 = lean_usize_to_nat(x_254);
x_256 = lean_nat_pow(x_7, x_255);
lean_dec(x_255);
x_257 = lean_usize_of_nat(x_256);
lean_dec(x_256);
x_258 = lean_usize_to_nat(x_257);
x_259 = lean_mk_empty_array_with_capacity(x_258);
lean_dec(x_258);
lean_inc(x_259);
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
lean_ctor_set(x_261, 2, x_239);
lean_ctor_set(x_261, 3, x_239);
lean_ctor_set_usize(x_261, 4, x_254);
x_262 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_262, 0, x_240);
lean_inc_n(x_241, 2);
x_263 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_263, 0, x_241);
lean_ctor_set(x_263, 1, x_241);
lean_ctor_set(x_263, 2, x_241);
lean_ctor_set(x_263, 3, x_262);
x_264 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_264, 0, x_247);
lean_ctor_set(x_264, 1, x_252);
lean_ctor_set(x_264, 2, x_238);
lean_ctor_set(x_264, 3, x_261);
lean_ctor_set(x_264, 4, x_263);
x_265 = lean_st_mk_ref(x_264, x_237);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_nat_add(x_8, x_7);
x_269 = lean_box(1);
x_270 = lean_box(1);
x_271 = lean_box(0);
x_272 = lean_box(2);
lean_inc(x_5);
x_273 = lean_array_get(x_5, x_6, x_268);
lean_dec(x_268);
x_274 = lean_box(0);
x_275 = lean_alloc_ctor(0, 0, 18);
x_276 = lean_unbox(x_274);
lean_ctor_set_uint8(x_275, 0, x_276);
x_277 = lean_unbox(x_274);
lean_ctor_set_uint8(x_275, 1, x_277);
x_278 = lean_unbox(x_274);
lean_ctor_set_uint8(x_275, 2, x_278);
x_279 = lean_unbox(x_274);
lean_ctor_set_uint8(x_275, 3, x_279);
x_280 = lean_unbox(x_274);
lean_ctor_set_uint8(x_275, 4, x_280);
x_281 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 5, x_281);
x_282 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 6, x_282);
x_283 = lean_unbox(x_274);
lean_ctor_set_uint8(x_275, 7, x_283);
x_284 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 8, x_284);
x_285 = lean_unbox(x_270);
lean_ctor_set_uint8(x_275, 9, x_285);
x_286 = lean_unbox(x_271);
lean_ctor_set_uint8(x_275, 10, x_286);
x_287 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 11, x_287);
x_288 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 12, x_288);
x_289 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 13, x_289);
x_290 = lean_unbox(x_272);
lean_ctor_set_uint8(x_275, 14, x_290);
x_291 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 15, x_291);
x_292 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 16, x_292);
x_293 = lean_unbox(x_269);
lean_ctor_set_uint8(x_275, 17, x_293);
x_294 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_275);
x_295 = lean_ctor_get(x_236, 0);
lean_inc(x_295);
lean_dec(x_236);
x_296 = lean_mk_empty_array_with_capacity(x_239);
x_297 = lean_box(0);
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_299, 0, x_275);
lean_ctor_set(x_299, 1, x_238);
lean_ctor_set(x_299, 2, x_295);
lean_ctor_set(x_299, 3, x_296);
lean_ctor_set(x_299, 4, x_297);
lean_ctor_set(x_299, 5, x_239);
lean_ctor_set(x_299, 6, x_298);
lean_ctor_set_uint64(x_299, sizeof(void*)*7, x_294);
x_300 = lean_unbox(x_274);
lean_ctor_set_uint8(x_299, sizeof(void*)*7 + 8, x_300);
x_301 = lean_unbox(x_274);
lean_ctor_set_uint8(x_299, sizeof(void*)*7 + 9, x_301);
x_302 = lean_unbox(x_274);
lean_ctor_set_uint8(x_299, sizeof(void*)*7 + 10, x_302);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_266);
x_303 = lean_whnf(x_273, x_299, x_266, x_13, x_14, x_267);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_st_ref_get(x_266, x_305);
lean_dec(x_266);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_153 = x_304;
x_154 = x_307;
goto block_234;
}
else
{
lean_dec(x_266);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_303, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_303, 1);
lean_inc(x_309);
lean_dec(x_303);
x_153 = x_308;
x_154 = x_309;
goto block_234;
}
else
{
uint8_t x_310; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_303);
if (x_310 == 0)
{
return x_303;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_303, 0);
x_312 = lean_ctor_get(x_303, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_303);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
block_25:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_mk_string_unchecked("code generator failed, unsupported occurrence of `", 50, 50);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_MessageData_ofName(x_1);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("`", 1, 1);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_23, x_12, x_13, x_14, x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_24;
}
block_36:
{
lean_object* x_28; 
lean_inc(x_14);
lean_inc(x_13);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_26, x_10, x_13, x_14, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_29, x_10, x_11, x_12, x_13, x_14, x_30);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
block_95:
{
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_16 = x_42;
goto block_25;
}
else
{
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_16 = x_42;
goto block_25;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_name_eq(x_46, x_48);
lean_dec(x_48);
lean_dec(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint64_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
x_50 = lean_st_ref_get(x_10, x_42);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_mk_ref(x_40, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(1);
x_57 = lean_box(1);
x_58 = lean_box(0);
x_59 = lean_box(2);
x_60 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_60, 0, x_49);
lean_ctor_set_uint8(x_60, 1, x_49);
lean_ctor_set_uint8(x_60, 2, x_49);
lean_ctor_set_uint8(x_60, 3, x_49);
lean_ctor_set_uint8(x_60, 4, x_49);
x_61 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 5, x_61);
x_62 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 6, x_62);
lean_ctor_set_uint8(x_60, 7, x_49);
x_63 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 8, x_63);
x_64 = lean_unbox(x_57);
lean_ctor_set_uint8(x_60, 9, x_64);
x_65 = lean_unbox(x_58);
lean_ctor_set_uint8(x_60, 10, x_65);
x_66 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 11, x_66);
x_67 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 12, x_67);
x_68 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 13, x_68);
x_69 = lean_unbox(x_59);
lean_ctor_set_uint8(x_60, 14, x_69);
x_70 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 15, x_70);
x_71 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 16, x_71);
x_72 = lean_unbox(x_56);
lean_ctor_set_uint8(x_60, 17, x_72);
x_73 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_60);
x_74 = lean_ctor_get(x_51, 0);
lean_inc(x_74);
lean_dec(x_51);
x_75 = lean_mk_empty_array_with_capacity(x_37);
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_78, 0, x_60);
lean_ctor_set(x_78, 1, x_38);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set(x_78, 3, x_75);
lean_ctor_set(x_78, 4, x_76);
lean_ctor_set(x_78, 5, x_37);
lean_ctor_set(x_78, 6, x_77);
lean_ctor_set_uint64(x_78, sizeof(void*)*7, x_73);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 8, x_49);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 9, x_49);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 10, x_49);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_54);
x_79 = lean_infer_type(x_2, x_78, x_54, x_13, x_14, x_55);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_st_ref_get(x_54, x_81);
lean_dec(x_54);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_26 = x_80;
x_27 = x_83;
goto block_36;
}
else
{
lean_dec(x_54);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_26 = x_84;
x_27 = x_85;
goto block_36;
}
else
{
uint8_t x_86; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_86 = !lean_is_exclusive(x_79);
if (x_86 == 0)
{
return x_79;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_79, 0);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_79);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
x_90 = lean_nat_add(x_3, x_4);
x_91 = lean_array_get(x_5, x_6, x_3);
x_92 = lean_ctor_get(x_43, 4);
lean_inc(x_92);
lean_dec(x_43);
lean_inc(x_90);
x_93 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0), 10, 4);
lean_closure_set(x_93, 0, x_91);
lean_closure_set(x_93, 1, x_92);
lean_closure_set(x_93, 2, x_6);
lean_closure_set(x_93, 3, x_90);
x_94 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_90, x_93, x_10, x_11, x_12, x_13, x_14, x_42);
lean_dec(x_90);
return x_94;
}
}
}
}
block_152:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint64_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; lean_object* x_141; 
x_102 = lean_st_ref_get(x_10, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_99);
x_105 = lean_st_mk_ref(x_99, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_box(1);
x_109 = lean_box(1);
x_110 = lean_box(0);
x_111 = lean_box(2);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 0, 18);
x_114 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, 0, x_114);
x_115 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, 1, x_115);
x_116 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, 2, x_116);
x_117 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, 3, x_117);
x_118 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, 4, x_118);
x_119 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 5, x_119);
x_120 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 6, x_120);
x_121 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, 7, x_121);
x_122 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 8, x_122);
x_123 = lean_unbox(x_109);
lean_ctor_set_uint8(x_113, 9, x_123);
x_124 = lean_unbox(x_110);
lean_ctor_set_uint8(x_113, 10, x_124);
x_125 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 11, x_125);
x_126 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 12, x_126);
x_127 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 13, x_127);
x_128 = lean_unbox(x_111);
lean_ctor_set_uint8(x_113, 14, x_128);
x_129 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 15, x_129);
x_130 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 16, x_130);
x_131 = lean_unbox(x_108);
lean_ctor_set_uint8(x_113, 17, x_131);
x_132 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_113);
x_133 = lean_ctor_get(x_103, 0);
lean_inc(x_133);
lean_dec(x_103);
x_134 = lean_mk_empty_array_with_capacity(x_96);
x_135 = lean_box(0);
x_136 = lean_box(0);
lean_inc(x_96);
lean_inc(x_97);
x_137 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_137, 0, x_113);
lean_ctor_set(x_137, 1, x_97);
lean_ctor_set(x_137, 2, x_133);
lean_ctor_set(x_137, 3, x_134);
lean_ctor_set(x_137, 4, x_135);
lean_ctor_set(x_137, 5, x_96);
lean_ctor_set(x_137, 6, x_136);
lean_ctor_set_uint64(x_137, sizeof(void*)*7, x_132);
x_138 = lean_unbox(x_112);
lean_ctor_set_uint8(x_137, sizeof(void*)*7 + 8, x_138);
x_139 = lean_unbox(x_112);
lean_ctor_set_uint8(x_137, sizeof(void*)*7 + 9, x_139);
x_140 = lean_unbox(x_112);
lean_ctor_set_uint8(x_137, sizeof(void*)*7 + 10, x_140);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_106);
x_141 = l_Lean_Meta_isConstructorApp_x3f(x_98, x_137, x_106, x_13, x_14, x_107);
lean_dec(x_137);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_st_ref_get(x_106, x_143);
lean_dec(x_106);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_37 = x_96;
x_38 = x_97;
x_39 = x_100;
x_40 = x_99;
x_41 = x_142;
x_42 = x_145;
goto block_95;
}
else
{
lean_dec(x_106);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_141, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
lean_dec(x_141);
x_37 = x_96;
x_38 = x_97;
x_39 = x_100;
x_40 = x_99;
x_41 = x_146;
x_42 = x_147;
goto block_95;
}
else
{
uint8_t x_148; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_141);
if (x_148 == 0)
{
return x_141;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_141, 0);
x_150 = lean_ctor_get(x_141, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_141);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
block_234:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; size_t x_174; lean_object* x_175; lean_object* x_176; size_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint64_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; lean_object* x_223; 
x_155 = lean_st_ref_get(x_10, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_box(0);
x_159 = lean_unsigned_to_nat(0u);
x_160 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_160);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
lean_inc(x_160);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_160);
lean_inc(x_160);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_160);
lean_inc(x_160);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_160);
lean_inc(x_160);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_160);
lean_inc(x_160);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_160);
lean_inc(x_161);
x_167 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_159);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_161);
lean_ctor_set(x_167, 4, x_162);
lean_ctor_set(x_167, 5, x_163);
lean_ctor_set(x_167, 6, x_164);
lean_ctor_set(x_167, 7, x_165);
lean_ctor_set(x_167, 8, x_166);
lean_inc(x_160);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_160);
lean_inc(x_160);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_160);
lean_inc(x_160);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_160);
lean_inc(x_160);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_160);
lean_inc(x_171);
lean_inc(x_168);
x_172 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_168);
lean_ctor_set(x_172, 4, x_171);
lean_ctor_set(x_172, 5, x_171);
x_173 = lean_unsigned_to_nat(5u);
x_174 = lean_usize_of_nat(x_173);
x_175 = lean_usize_to_nat(x_174);
x_176 = lean_nat_pow(x_7, x_175);
lean_dec(x_175);
x_177 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_178 = lean_usize_to_nat(x_177);
x_179 = lean_mk_empty_array_with_capacity(x_178);
lean_dec(x_178);
lean_inc(x_179);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
lean_ctor_set(x_181, 2, x_159);
lean_ctor_set(x_181, 3, x_159);
lean_ctor_set_usize(x_181, 4, x_174);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_160);
lean_inc_n(x_161, 2);
x_183 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_183, 0, x_161);
lean_ctor_set(x_183, 1, x_161);
lean_ctor_set(x_183, 2, x_161);
lean_ctor_set(x_183, 3, x_182);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_167);
lean_ctor_set(x_184, 1, x_172);
lean_ctor_set(x_184, 2, x_158);
lean_ctor_set(x_184, 3, x_181);
lean_ctor_set(x_184, 4, x_183);
lean_inc(x_184);
x_185 = lean_st_mk_ref(x_184, x_157);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Expr_toCtorIfLit(x_153);
x_189 = lean_box(1);
x_190 = lean_box(1);
x_191 = lean_box(0);
x_192 = lean_box(2);
x_193 = l_Lean_Expr_toCtorIfLit(x_9);
x_194 = lean_box(0);
x_195 = lean_alloc_ctor(0, 0, 18);
x_196 = lean_unbox(x_194);
lean_ctor_set_uint8(x_195, 0, x_196);
x_197 = lean_unbox(x_194);
lean_ctor_set_uint8(x_195, 1, x_197);
x_198 = lean_unbox(x_194);
lean_ctor_set_uint8(x_195, 2, x_198);
x_199 = lean_unbox(x_194);
lean_ctor_set_uint8(x_195, 3, x_199);
x_200 = lean_unbox(x_194);
lean_ctor_set_uint8(x_195, 4, x_200);
x_201 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 5, x_201);
x_202 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 6, x_202);
x_203 = lean_unbox(x_194);
lean_ctor_set_uint8(x_195, 7, x_203);
x_204 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 8, x_204);
x_205 = lean_unbox(x_190);
lean_ctor_set_uint8(x_195, 9, x_205);
x_206 = lean_unbox(x_191);
lean_ctor_set_uint8(x_195, 10, x_206);
x_207 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 11, x_207);
x_208 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 12, x_208);
x_209 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 13, x_209);
x_210 = lean_unbox(x_192);
lean_ctor_set_uint8(x_195, 14, x_210);
x_211 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 15, x_211);
x_212 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 16, x_212);
x_213 = lean_unbox(x_189);
lean_ctor_set_uint8(x_195, 17, x_213);
x_214 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_195);
x_215 = lean_ctor_get(x_156, 0);
lean_inc(x_215);
lean_dec(x_156);
x_216 = lean_mk_empty_array_with_capacity(x_159);
x_217 = lean_box(0);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_219, 0, x_195);
lean_ctor_set(x_219, 1, x_158);
lean_ctor_set(x_219, 2, x_215);
lean_ctor_set(x_219, 3, x_216);
lean_ctor_set(x_219, 4, x_217);
lean_ctor_set(x_219, 5, x_159);
lean_ctor_set(x_219, 6, x_218);
lean_ctor_set_uint64(x_219, sizeof(void*)*7, x_214);
x_220 = lean_unbox(x_194);
lean_ctor_set_uint8(x_219, sizeof(void*)*7 + 8, x_220);
x_221 = lean_unbox(x_194);
lean_ctor_set_uint8(x_219, sizeof(void*)*7 + 9, x_221);
x_222 = lean_unbox(x_194);
lean_ctor_set_uint8(x_219, sizeof(void*)*7 + 10, x_222);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_186);
x_223 = l_Lean_Meta_isConstructorApp_x3f(x_193, x_219, x_186, x_13, x_14, x_187);
lean_dec(x_219);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_st_ref_get(x_186, x_225);
lean_dec(x_186);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_96 = x_159;
x_97 = x_158;
x_98 = x_188;
x_99 = x_184;
x_100 = x_224;
x_101 = x_227;
goto block_152;
}
else
{
lean_dec(x_186);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_223, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 1);
lean_inc(x_229);
lean_dec(x_223);
x_96 = x_159;
x_97 = x_158;
x_98 = x_188;
x_99 = x_184;
x_100 = x_228;
x_101 = x_229;
goto block_152;
}
else
{
uint8_t x_230; 
lean_dec(x_188);
lean_dec(x_184);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_223);
if (x_230 == 0)
{
return x_223;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_223, 0);
x_232 = lean_ctor_get(x_223, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_223);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
lean_inc(x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_15);
lean_inc(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
lean_inc(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_15);
lean_inc(x_16);
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set(x_22, 7, x_20);
lean_ctor_set(x_22, 8, x_21);
lean_inc(x_15);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_15);
lean_inc(x_15);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_15);
lean_inc(x_15);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_15);
lean_inc(x_15);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_15);
lean_inc(x_26);
lean_inc(x_23);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_26);
x_28 = lean_unsigned_to_nat(5u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_nat_pow(x_1, x_30);
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
lean_ctor_set(x_36, 2, x_14);
lean_ctor_set(x_36, 3, x_14);
lean_ctor_set_usize(x_36, 4, x_29);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_15);
lean_inc_n(x_16, 2);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_16);
lean_ctor_set(x_38, 2, x_16);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_13);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_st_mk_ref(x_39, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(1);
x_44 = lean_box(1);
x_45 = lean_box(0);
x_46 = lean_box(2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 0, 18);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 0, x_49);
x_50 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 1, x_50);
x_51 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 2, x_51);
x_52 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 3, x_52);
x_53 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 4, x_53);
x_54 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 5, x_54);
x_55 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 6, x_55);
x_56 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 7, x_56);
x_57 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 8, x_57);
x_58 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 9, x_58);
x_59 = lean_unbox(x_45);
lean_ctor_set_uint8(x_48, 10, x_59);
x_60 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 11, x_60);
x_61 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 12, x_61);
x_62 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 13, x_62);
x_63 = lean_unbox(x_46);
lean_ctor_set_uint8(x_48, 14, x_63);
x_64 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 15, x_64);
x_65 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 16, x_65);
x_66 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 17, x_66);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_48);
x_68 = lean_ctor_get(x_11, 0);
lean_inc(x_68);
lean_dec(x_11);
x_69 = lean_mk_empty_array_with_capacity(x_14);
x_70 = lean_box(0);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_13);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_69);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_14);
lean_ctor_set(x_72, 6, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*7, x_67);
x_73 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 8, x_73);
x_74 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 9, x_74);
x_75 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 10, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_41);
x_76 = lean_whnf(x_2, x_72, x_41, x_7, x_8, x_42);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_st_ref_get(x_41, x_78);
lean_dec(x_41);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_apply_7(x_3, x_77, x_4, x_5, x_6, x_7, x_8, x_80);
return x_81;
}
else
{
lean_dec(x_41);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_apply_7(x_3, x_82, x_4, x_5, x_6, x_7, x_8, x_83);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_76);
if (x_85 == 0)
{
return x_76;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_76, 0);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_76);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Name_getPrefix(x_9);
x_11 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_add(x_20, x_21);
x_23 = lean_nat_add(x_22, x_19);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Expr_sort___override(x_24);
x_26 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_26);
x_27 = lean_mk_array(x_26, x_25);
x_28 = lean_nat_sub(x_26, x_19);
lean_dec(x_26);
lean_inc(x_1);
x_29 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_27, x_28);
lean_inc(x_29);
lean_inc(x_23);
lean_inc(x_1);
x_30 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed), 15, 8);
lean_closure_set(x_30, 0, x_9);
lean_closure_set(x_30, 1, x_1);
lean_closure_set(x_30, 2, x_23);
lean_closure_set(x_30, 3, x_19);
lean_closure_set(x_30, 4, x_15);
lean_closure_set(x_30, 5, x_29);
lean_closure_set(x_30, 6, x_21);
lean_closure_set(x_30, 7, x_18);
x_31 = lean_array_get(x_15, x_29, x_20);
lean_dec(x_20);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2___boxed), 9, 3);
lean_closure_set(x_32, 0, x_21);
lean_closure_set(x_32, 1, x_31);
lean_closure_set(x_32, 2, x_30);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_23, x_32, x_2, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_36 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitNoConfusion", 49, 49);
x_37 = lean_unsigned_to_nat(652u);
x_38 = lean_unsigned_to_nat(56u);
x_39 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_40 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
x_41 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_40, x_2, x_3, x_4, x_5, x_6, x_34);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_8);
lean_dec(x_1);
x_46 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_47 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitNoConfusion", 49, 49);
x_48 = lean_unsigned_to_nat(650u);
x_49 = lean_unsigned_to_nat(42u);
x_50 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_51 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_46, x_47, x_48, x_49, x_50);
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_46);
x_52 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_51, x_2, x_3, x_4, x_5, x_6, x_7);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Expr_getAppNumArgs(x_1);
x_11 = lean_nat_dec_lt(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_1);
x_12 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_nat_sub(x_2, x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_13, x_4, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_15, x_4, x_5, x_6, x_7, x_8, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_sort___override(x_12);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_nat_dec_lt(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
lean_dec(x_3);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 2);
lean_inc(x_35);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_18);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_11);
x_40 = lean_mk_array(x_11, x_13);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_11, x_41);
lean_dec(x_11);
x_43 = l_Lean_instInhabitedExpr;
lean_inc(x_1);
x_44 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_40, x_42);
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_array_fget(x_45, x_34);
x_47 = lean_array_get(x_43, x_44, x_4);
lean_dec(x_44);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_32, x_46, x_47, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_nat_add(x_34, x_41);
lean_dec(x_34);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_35);
x_56 = l_Lean_Compiler_LCNF_joinTypes(x_52, x_30);
x_57 = lean_array_push(x_29, x_53);
lean_ctor_set(x_49, 1, x_56);
lean_ctor_set(x_49, 0, x_57);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_49);
lean_ctor_set(x_18, 0, x_33);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_18);
x_59 = lean_ctor_get(x_2, 2);
x_60 = lean_nat_add(x_4, x_59);
lean_dec(x_4);
x_3 = x_58;
x_4 = x_60;
x_10 = x_50;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_ctor_get(x_49, 0);
x_63 = lean_ctor_get(x_49, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_49);
x_64 = lean_nat_add(x_34, x_41);
lean_dec(x_34);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_45);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_35);
x_66 = l_Lean_Compiler_LCNF_joinTypes(x_62, x_30);
x_67 = lean_array_push(x_29, x_63);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_68);
lean_ctor_set(x_18, 0, x_33);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_18);
x_70 = lean_ctor_get(x_2, 2);
x_71 = lean_nat_add(x_4, x_70);
lean_dec(x_4);
x_3 = x_69;
x_4 = x_71;
x_10 = x_50;
goto _start;
}
}
else
{
uint8_t x_73; 
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_18);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_48);
if (x_73 == 0)
{
return x_48;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_48, 0);
x_75 = lean_ctor_get(x_48, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_48);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_18, 0);
x_78 = lean_ctor_get(x_18, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_18);
x_79 = lean_ctor_get(x_27, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_27, 2);
lean_inc(x_80);
x_81 = lean_nat_dec_lt(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_29);
lean_ctor_set(x_82, 1, x_30);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_27);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_10);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_inc(x_11);
x_86 = lean_mk_array(x_11, x_13);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_11, x_87);
lean_dec(x_11);
x_89 = l_Lean_instInhabitedExpr;
lean_inc(x_1);
x_90 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_86, x_88);
x_91 = lean_ctor_get(x_27, 0);
lean_inc(x_91);
lean_dec(x_27);
x_92 = lean_array_fget(x_91, x_79);
x_93 = lean_array_get(x_89, x_90, x_4);
lean_dec(x_90);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_94 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_77, x_92, x_93, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
x_100 = lean_nat_add(x_79, x_87);
lean_dec(x_79);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_80);
x_102 = l_Lean_Compiler_LCNF_joinTypes(x_97, x_30);
x_103 = lean_array_push(x_29, x_98);
if (lean_is_scalar(x_99)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_99;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_78);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_ctor_get(x_2, 2);
x_108 = lean_nat_add(x_4, x_107);
lean_dec(x_4);
x_3 = x_106;
x_4 = x_108;
x_10 = x_96;
goto _start;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_91);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_110 = lean_ctor_get(x_94, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_94, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_112 = x_94;
} else {
 lean_dec_ref(x_94);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_6, x_7, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_CasesInfo_numAlts(x_1);
x_17 = lean_nat_dec_eq(x_16, x_2);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_array_get(x_18, x_3, x_19);
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_20, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = l_Lean_Name_getPrefix(x_25);
lean_inc(x_26);
x_27 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_26, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 5)
{
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_25);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_mk_empty_array_with_capacity(x_2);
x_34 = lean_ctor_get(x_1, 5);
lean_inc(x_34);
x_35 = lean_array_get_size(x_34);
x_36 = l_Array_toSubarray___redArg(x_34, x_2, x_35);
x_37 = lean_ctor_get(x_30, 4);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_ctor_get(x_1, 4);
lean_inc(x_38);
lean_dec(x_1);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 0, x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_21);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_42 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_4, x_38, x_40, x_41, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
lean_inc(x_48);
x_49 = l_Lean_Compiler_LCNF_mkAuxParam(x_48, x_17, x_8, x_9, x_10, x_11, x_46);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_26);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_32);
lean_ctor_set(x_53, 3, x_47);
lean_inc(x_51);
lean_ctor_set_tag(x_49, 3);
lean_ctor_set(x_49, 1, x_53);
x_54 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_49, x_7, x_52);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec(x_51);
lean_ctor_set(x_23, 0, x_56);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_23, x_3, x_5, x_7, x_8, x_9, x_10, x_11, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_26);
lean_ctor_set(x_60, 1, x_48);
lean_ctor_set(x_60, 2, x_32);
lean_ctor_set(x_60, 3, x_47);
lean_inc(x_58);
x_61 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_61, x_7, x_59);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
lean_ctor_set(x_23, 0, x_64);
x_65 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_23, x_3, x_5, x_7, x_8, x_9, x_10, x_11, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_free_object(x_23);
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_66 = !lean_is_exclusive(x_42);
if (x_66 == 0)
{
return x_42;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_42, 0);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_42);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_23, 0);
lean_inc(x_70);
lean_dec(x_23);
x_71 = lean_mk_empty_array_with_capacity(x_2);
x_72 = lean_ctor_get(x_1, 5);
lean_inc(x_72);
x_73 = lean_array_get_size(x_72);
x_74 = l_Array_toSubarray___redArg(x_72, x_2, x_73);
x_75 = lean_ctor_get(x_30, 4);
lean_inc(x_75);
lean_dec(x_30);
x_76 = lean_ctor_get(x_1, 4);
lean_inc(x_76);
lean_dec(x_1);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 0, x_71);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_21);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_80 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_4, x_76, x_78, x_79, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_76);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
lean_inc(x_86);
x_87 = l_Lean_Compiler_LCNF_mkAuxParam(x_86, x_17, x_8, x_9, x_10, x_11, x_84);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_26);
lean_ctor_set(x_91, 1, x_86);
lean_ctor_set(x_91, 2, x_70);
lean_ctor_set(x_91, 3, x_85);
lean_inc(x_88);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(3, 2, 0);
} else {
 x_92 = x_90;
 lean_ctor_set_tag(x_92, 3);
}
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_92, x_7, x_89);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_96, x_3, x_5, x_7, x_8, x_9, x_10, x_11, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_70);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
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
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_27, 1);
lean_inc(x_102);
lean_dec(x_27);
x_103 = lean_mk_string_unchecked("unsupported `", 13, 13);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = l_Lean_MessageData_ofName(x_25);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_105);
lean_ctor_set(x_21, 0, x_104);
x_106 = lean_mk_string_unchecked("` application during code generation", 36, 36);
x_107 = l_Lean_stringToMessageData(x_106);
lean_dec(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_21);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_108, x_9, x_10, x_11, x_102);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_ctor_get(x_27, 1);
lean_inc(x_110);
lean_dec(x_27);
x_111 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_112 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCases", 43, 43);
x_113 = lean_unsigned_to_nat(552u);
x_114 = lean_unsigned_to_nat(57u);
x_115 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_116 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_111, x_112, x_113, x_114, x_115);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_111);
x_117 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_116, x_7, x_8, x_9, x_10, x_11, x_110);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_27);
if (x_118 == 0)
{
return x_27;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_27, 0);
x_120 = lean_ctor_get(x_27, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_27);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_21, 0);
x_123 = lean_ctor_get(x_21, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_21);
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
x_125 = l_Lean_Name_getPrefix(x_124);
lean_inc(x_125);
x_126 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_125, x_7, x_8, x_9, x_10, x_11, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 5)
{
if (lean_obj_tag(x_122) == 1)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_124);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_122, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_131 = x_122;
} else {
 lean_dec_ref(x_122);
 x_131 = lean_box(0);
}
x_132 = lean_mk_empty_array_with_capacity(x_2);
x_133 = lean_ctor_get(x_1, 5);
lean_inc(x_133);
x_134 = lean_array_get_size(x_133);
x_135 = l_Array_toSubarray___redArg(x_133, x_2, x_134);
x_136 = lean_ctor_get(x_129, 4);
lean_inc(x_136);
lean_dec(x_129);
x_137 = lean_ctor_get(x_1, 4);
lean_inc(x_137);
lean_dec(x_1);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_14);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_142 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_4, x_137, x_140, x_141, x_7, x_8, x_9, x_10, x_11, x_128);
lean_dec(x_137);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
lean_dec(x_142);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
lean_inc(x_148);
x_149 = l_Lean_Compiler_LCNF_mkAuxParam(x_148, x_17, x_8, x_9, x_10, x_11, x_146);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_153, 0, x_125);
lean_ctor_set(x_153, 1, x_148);
lean_ctor_set(x_153, 2, x_130);
lean_ctor_set(x_153, 3, x_147);
lean_inc(x_150);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(3, 2, 0);
} else {
 x_154 = x_152;
 lean_ctor_set_tag(x_154, 3);
}
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_154, x_7, x_151);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_ctor_get(x_150, 0);
lean_inc(x_157);
lean_dec(x_150);
if (lean_is_scalar(x_131)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_131;
}
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_158, x_3, x_5, x_7, x_8, x_9, x_10, x_11, x_156);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_125);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_160 = lean_ctor_get(x_142, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_142, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_162 = x_142;
} else {
 lean_dec_ref(x_142);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_126, 1);
lean_inc(x_164);
lean_dec(x_126);
x_165 = lean_mk_string_unchecked("unsupported `", 13, 13);
x_166 = l_Lean_stringToMessageData(x_165);
lean_dec(x_165);
x_167 = l_Lean_MessageData_ofName(x_124);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_mk_string_unchecked("` application during code generation", 36, 36);
x_170 = l_Lean_stringToMessageData(x_169);
lean_dec(x_169);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_171, x_9, x_10, x_11, x_164);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_126, 1);
lean_inc(x_173);
lean_dec(x_126);
x_174 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_175 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCases", 43, 43);
x_176 = lean_unsigned_to_nat(552u);
x_177 = lean_unsigned_to_nat(57u);
x_178 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_179 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_174, x_175, x_176, x_177, x_178);
lean_dec(x_178);
lean_dec(x_175);
lean_dec(x_174);
x_180 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_179, x_7, x_8, x_9, x_10, x_11, x_173);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_ctor_get(x_126, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_126, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_183 = x_126;
} else {
 lean_dec_ref(x_126);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
else
{
lean_object* x_185; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_185 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_14, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_185;
}
}
else
{
uint8_t x_186; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_13);
if (x_186 == 0)
{
return x_13;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_13, 0);
x_188 = lean_ctor_get(x_13, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_13);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
lean_inc(x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_14);
lean_inc(x_14);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
lean_inc(x_14);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
lean_inc(x_15);
lean_inc_n(x_1, 3);
x_21 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_1);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_17);
lean_ctor_set(x_21, 6, x_18);
lean_ctor_set(x_21, 7, x_19);
lean_ctor_set(x_21, 8, x_20);
lean_inc(x_14);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_14);
lean_inc(x_14);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_14);
lean_inc(x_14);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_14);
lean_inc(x_14);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_14);
lean_inc(x_25);
lean_inc(x_22);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_25);
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
lean_inc_n(x_1, 2);
x_36 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_1);
lean_ctor_set(x_36, 3, x_1);
lean_ctor_set_usize(x_36, 4, x_29);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_14);
lean_inc_n(x_15, 2);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_15);
lean_ctor_set(x_38, 2, x_15);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_13);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_st_mk_ref(x_39, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(1);
x_44 = lean_box(1);
x_45 = lean_box(0);
x_46 = lean_box(2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 0, 18);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 0, x_49);
x_50 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 1, x_50);
x_51 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 2, x_51);
x_52 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 3, x_52);
x_53 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 4, x_53);
x_54 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 5, x_54);
x_55 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 6, x_55);
x_56 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 7, x_56);
x_57 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 8, x_57);
x_58 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 9, x_58);
x_59 = lean_unbox(x_45);
lean_ctor_set_uint8(x_48, 10, x_59);
x_60 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 11, x_60);
x_61 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 12, x_61);
x_62 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 13, x_62);
x_63 = lean_unbox(x_46);
lean_ctor_set_uint8(x_48, 14, x_63);
x_64 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 15, x_64);
x_65 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 16, x_65);
x_66 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 17, x_66);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_48);
x_68 = lean_ctor_get(x_11, 0);
lean_inc(x_68);
lean_dec(x_11);
x_69 = lean_mk_empty_array_with_capacity(x_1);
x_70 = lean_box(0);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_13);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_69);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_1);
lean_ctor_set(x_72, 6, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*7, x_67);
x_73 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 8, x_73);
x_74 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 9, x_74);
x_75 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 10, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_41);
x_76 = lean_infer_type(x_2, x_72, x_41, x_7, x_8, x_42);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_st_ref_get(x_41, x_78);
lean_dec(x_41);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_apply_7(x_3, x_77, x_4, x_5, x_6, x_7, x_8, x_80);
return x_81;
}
else
{
lean_dec(x_41);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_apply_7(x_3, x_82, x_4, x_5, x_6, x_7, x_8, x_83);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_76);
if (x_85 == 0)
{
return x_76;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_76, 0);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_76);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_sort___override(x_10);
x_12 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
lean_inc(x_2);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_13, x_15);
x_17 = l_Lean_Expr_getAppFn(x_2);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed), 12, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_16);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_9);
lean_inc(x_9);
x_20 = l_Array_toSubarray___redArg(x_16, x_18, x_9);
x_21 = l_Array_ofSubarray___redArg(x_20);
lean_dec(x_20);
x_22 = l_Lean_mkAppN(x_17, x_21);
lean_dec(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1), 9, 3);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_22);
lean_closure_set(x_23, 2, x_19);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_9, x_23, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_nat_dec_lt(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_push(x_3, x_16);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_20;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_eq(x_10, x_3);
if (x_11 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_2, x_17, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_mk_string_unchecked("_x", 2, 2);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_21, x_23, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
default: 
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = l_Lean_Compiler_LCNF_Param_toExpr(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Compiler_LCNF_inferType(x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_16, x_4, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_38; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_uset(x_3, x_2, x_13);
x_38 = lean_unbox(x_19);
lean_dec(x_19);
if (x_38 == 0)
{
lean_inc(x_6);
x_22 = x_4;
x_23 = x_6;
x_24 = x_20;
goto block_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_39 = lean_st_ref_take(x_4, x_20);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 5);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get(x_12, 0);
lean_inc(x_48);
x_49 = l_Lean_FVarIdSet_insert(x_47, x_48);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_49);
x_51 = lean_st_ref_set(x_4, x_50, x_41);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_6);
x_22 = x_4;
x_23 = x_6;
x_24 = x_52;
goto block_37;
}
block_37:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_12, 2);
lean_inc(x_25);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_25, x_22, x_24);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_12, x_27, x_23, x_28);
lean_dec(x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_add(x_2, x_33);
x_35 = lean_array_uset(x_21, x_2, x_30);
x_2 = x_34;
x_3 = x_35;
x_9 = x_31;
goto _start;
}
}
else
{
uint8_t x_53; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
return x_18;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_18, 0);
x_55 = lean_ctor_get(x_18, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_18);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
return x_15;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_15, 0);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_15);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_57; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_array_get_size(x_60);
x_63 = lean_nat_dec_lt(x_62, x_2);
if (x_63 == 0)
{
lean_dec(x_62);
lean_dec(x_2);
x_10 = x_61;
x_11 = x_60;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_59;
goto block_56;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_nat_sub(x_2, x_62);
lean_dec(x_62);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_61, x_64, x_4, x_7, x_8, x_59);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_8);
lean_inc(x_7);
x_68 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_66, x_4, x_5, x_6, x_7, x_8, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Array_append(lean_box(0), x_60, x_71);
lean_dec(x_71);
x_10 = x_72;
x_11 = x_73;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_70;
goto block_56;
}
else
{
uint8_t x_74; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_68);
if (x_74 == 0)
{
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_68, 0);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_68);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_65);
if (x_78 == 0)
{
return x_65;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_65, 0);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_65);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_57);
if (x_82 == 0)
{
return x_57;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_57, 0);
x_84 = lean_ctor_get(x_57, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_57);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
block_56:
{
size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_array_size(x_11);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_21 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(x_18, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_10, x_12, x_13, x_14, x_15, x_16, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_25, x_12, x_13, x_14, x_15, x_16, x_26);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = l_Lean_Compiler_LCNF_Code_inferType(x_28, x_13, x_14, x_15, x_16, x_29);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_37, 2, x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_27, 0);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_27);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_24);
if (x_48 == 0)
{
return x_24;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_24, 0);
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_24);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_21, 0);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_21);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0), 9, 3);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_1);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__0(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_name_eq(x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = lean_expr_eqv(x_8, x_9);
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
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_array_get(x_9, x_2, x_10);
x_12 = lean_array_uget(x_7, x_6);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_7, x_6, x_13);
x_22 = l_Lean_Expr_getAppFn(x_12);
x_23 = l_Lean_Expr_constName_x3f(x_22);
lean_dec(x_22);
lean_inc(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__0(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
if (x_25 == 0)
{
if (x_25 == 0)
{
lean_dec(x_11);
x_15 = x_12;
goto block_21;
}
else
{
lean_dec(x_12);
x_15 = x_11;
goto block_21;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_box(0);
x_27 = l_Lean_Expr_sort___override(x_26);
x_28 = l_Lean_Expr_getAppNumArgs(x_12);
lean_inc(x_28);
x_29 = lean_mk_array(x_28, x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_28, x_30);
lean_dec(x_28);
lean_inc(x_12);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_29, x_31);
x_33 = lean_array_get_size(x_32);
x_34 = lean_array_get_size(x_4);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_11);
x_15 = x_12;
goto block_21;
}
else
{
uint8_t x_36; 
x_36 = l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___redArg(x_32, x_4, x_33);
lean_dec(x_32);
if (x_36 == 0)
{
lean_dec(x_11);
x_15 = x_12;
goto block_21;
}
else
{
lean_dec(x_12);
x_15 = x_11;
goto block_21;
}
}
}
block_21:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_6, x_17);
x_19 = lean_array_uset(x_14, x_6, x_15);
x_6 = x_18;
x_7 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_array_get(x_9, x_2, x_10);
x_12 = lean_array_uget(x_7, x_6);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_7, x_6, x_13);
x_22 = l_Lean_Expr_getAppFn(x_12);
x_23 = l_Lean_Expr_constName_x3f(x_22);
lean_dec(x_22);
lean_inc(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__0(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
if (x_25 == 0)
{
if (x_25 == 0)
{
lean_dec(x_11);
x_15 = x_12;
goto block_21;
}
else
{
lean_dec(x_12);
x_15 = x_11;
goto block_21;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_box(0);
x_27 = l_Lean_Expr_sort___override(x_26);
x_28 = l_Lean_Expr_getAppNumArgs(x_12);
lean_inc(x_28);
x_29 = lean_mk_array(x_28, x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_28, x_30);
lean_dec(x_28);
lean_inc(x_12);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_12, x_29, x_31);
x_33 = lean_array_get_size(x_32);
x_34 = lean_array_get_size(x_4);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_11);
x_15 = x_12;
goto block_21;
}
else
{
uint8_t x_36; 
x_36 = l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___redArg(x_32, x_4, x_33);
lean_dec(x_32);
if (x_36 == 0)
{
lean_dec(x_11);
x_15 = x_12;
goto block_21;
}
else
{
lean_dec(x_12);
x_15 = x_11;
goto block_21;
}
}
}
block_21:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_6, x_17);
x_19 = lean_array_uset(x_14, x_6, x_15);
x_20 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_18, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg___lam__0), 8, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_unbox(x_11);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_13, x_12, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_13 = l_Lean_Expr_getAppFn(x_7);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_sort___override(x_14);
x_16 = l_Lean_Expr_getAppNumArgs(x_7);
lean_inc(x_16);
x_17 = lean_mk_array(x_16, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_16, x_18);
lean_dec(x_16);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_7, x_17, x_19);
x_21 = lean_array_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
x_24 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2(x_1, x_2, x_3, x_6, x_21, x_23, x_20);
x_25 = l_Lean_mkAppN(x_13, x_24);
lean_dec(x_24);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Meta_mkLambdaFVars(x_6, x_25, x_4, x_5, x_4, x_27, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_6, x_12);
if (x_13 == 1)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; uint8_t x_24; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
lean_dec(x_6);
x_23 = lean_array_fget(x_5, x_7);
x_95 = lean_ctor_get(x_1, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_nat_dec_le(x_96, x_7);
lean_dec(x_96);
if (x_97 == 0)
{
lean_dec(x_95);
x_24 = x_97;
goto block_94;
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_nat_dec_lt(x_7, x_98);
lean_dec(x_98);
x_24 = x_99;
goto block_94;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_20 = lean_array_push(x_8, x_17);
x_6 = x_16;
x_7 = x_19;
x_8 = x_20;
x_11 = x_18;
goto _start;
}
block_94:
{
if (x_24 == 0)
{
x_17 = x_23;
x_18 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_25 = lean_ctor_get(x_1, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_ctor_get(x_2, 4);
x_29 = lean_box(0);
x_30 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_unsigned_to_nat(5u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_to_nat(x_33);
x_35 = lean_nat_pow(x_31, x_34);
lean_dec(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = lean_usize_to_nat(x_36);
x_38 = lean_mk_empty_array_with_capacity(x_37);
lean_dec(x_37);
lean_inc(x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_inc(x_30);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_30);
lean_inc(x_30);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_30);
lean_inc(x_30);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_30);
lean_inc(x_30);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_30);
lean_inc(x_30);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_30);
lean_inc(x_30);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_30);
lean_inc(x_40);
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_12);
lean_ctor_set(x_46, 2, x_12);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_43);
lean_ctor_set(x_46, 7, x_44);
lean_ctor_set(x_46, 8, x_45);
lean_inc(x_30);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_30);
lean_inc(x_30);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_30);
lean_inc(x_30);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_30);
lean_inc(x_30);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_30);
lean_inc(x_50);
lean_inc(x_47);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set(x_51, 3, x_47);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_51, 5, x_50);
lean_inc(x_38);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_38);
lean_inc(x_38);
x_53 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_12);
lean_ctor_set(x_53, 3, x_12);
lean_ctor_set_usize(x_53, 4, x_33);
lean_inc(x_30);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_30);
lean_inc_n(x_40, 2);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 2, x_40);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_29);
lean_ctor_set(x_56, 3, x_53);
lean_ctor_set(x_56, 4, x_55);
x_57 = lean_st_mk_ref(x_56, x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_nat_sub(x_7, x_26);
lean_dec(x_26);
lean_inc(x_60);
x_61 = l___private_Init_GetElem_0__List_get_x21Internal___redArg(x_27, x_28, x_60);
x_62 = lean_box(1);
x_63 = lean_box(0);
x_64 = lean_box(2);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_30);
x_66 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_66, 0, x_39);
lean_ctor_set(x_66, 1, x_38);
lean_ctor_set(x_66, 2, x_12);
lean_ctor_set(x_66, 3, x_12);
lean_ctor_set_usize(x_66, 4, x_33);
x_67 = l_instInhabitedNat;
x_68 = lean_ctor_get(x_1, 5);
lean_inc(x_68);
x_69 = lean_box(x_13);
x_70 = lean_box(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_71 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___lam__0___boxed), 12, 5);
lean_closure_set(x_71, 0, x_61);
lean_closure_set(x_71, 1, x_3);
lean_closure_set(x_71, 2, x_1);
lean_closure_set(x_71, 3, x_69);
lean_closure_set(x_71, 4, x_70);
x_72 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_72, 0, x_13);
lean_ctor_set_uint8(x_72, 1, x_13);
lean_ctor_set_uint8(x_72, 2, x_13);
lean_ctor_set_uint8(x_72, 3, x_13);
lean_ctor_set_uint8(x_72, 4, x_13);
lean_ctor_set_uint8(x_72, 5, x_4);
lean_ctor_set_uint8(x_72, 6, x_4);
lean_ctor_set_uint8(x_72, 7, x_13);
lean_ctor_set_uint8(x_72, 8, x_4);
x_73 = lean_unbox(x_62);
lean_ctor_set_uint8(x_72, 9, x_73);
x_74 = lean_unbox(x_63);
lean_ctor_set_uint8(x_72, 10, x_74);
lean_ctor_set_uint8(x_72, 11, x_4);
lean_ctor_set_uint8(x_72, 12, x_4);
lean_ctor_set_uint8(x_72, 13, x_4);
x_75 = lean_unbox(x_64);
lean_ctor_set_uint8(x_72, 14, x_75);
lean_ctor_set_uint8(x_72, 15, x_4);
lean_ctor_set_uint8(x_72, 16, x_4);
lean_ctor_set_uint8(x_72, 17, x_4);
x_76 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_72);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_66);
lean_ctor_set(x_77, 2, x_29);
x_78 = lean_mk_empty_array_with_capacity(x_12);
x_79 = lean_box(0);
x_80 = lean_box(0);
x_81 = lean_array_get(x_67, x_68, x_60);
lean_dec(x_60);
lean_dec(x_68);
x_82 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_29);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_12);
lean_ctor_set(x_82, 6, x_80);
lean_ctor_set_uint64(x_82, sizeof(void*)*7, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 8, x_13);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 9, x_13);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 10, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_58);
x_83 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg(x_23, x_81, x_71, x_13, x_82, x_58, x_9, x_10, x_59);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_get(x_58, x_85);
lean_dec(x_58);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_17 = x_84;
x_18 = x_87;
goto block_22;
}
else
{
lean_dec(x_58);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_17 = x_88;
x_18 = x_89;
goto block_22;
}
else
{
uint8_t x_90; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_83);
if (x_90 == 0)
{
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_83, 0);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_83);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_6, x_15);
if (x_16 == 1)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_6, x_18);
x_26 = lean_array_fget(x_5, x_7);
x_98 = lean_ctor_get(x_1, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_nat_dec_le(x_99, x_7);
lean_dec(x_99);
if (x_100 == 0)
{
lean_dec(x_98);
x_27 = x_100;
goto block_97;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_nat_dec_lt(x_7, x_101);
lean_dec(x_101);
x_27 = x_102;
goto block_97;
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_nat_add(x_7, x_18);
x_23 = lean_array_push(x_8, x_20);
x_24 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_19, x_22, x_23, x_12, x_13, x_21);
return x_24;
}
block_97:
{
if (x_27 == 0)
{
x_20 = x_26;
x_21 = x_14;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_28 = lean_ctor_get(x_1, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_ctor_get(x_2, 4);
x_32 = lean_box(0);
x_33 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_unsigned_to_nat(5u);
x_36 = lean_usize_of_nat(x_35);
x_37 = lean_usize_to_nat(x_36);
x_38 = lean_nat_pow(x_34, x_37);
lean_dec(x_37);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = lean_usize_to_nat(x_39);
x_41 = lean_mk_empty_array_with_capacity(x_40);
lean_dec(x_40);
lean_inc(x_41);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_inc(x_33);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_33);
lean_inc(x_33);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_33);
lean_inc(x_33);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_33);
lean_inc(x_33);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_33);
lean_inc(x_33);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_33);
lean_inc(x_33);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_33);
lean_inc(x_43);
x_49 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_15);
lean_ctor_set(x_49, 2, x_15);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set(x_49, 4, x_44);
lean_ctor_set(x_49, 5, x_45);
lean_ctor_set(x_49, 6, x_46);
lean_ctor_set(x_49, 7, x_47);
lean_ctor_set(x_49, 8, x_48);
lean_inc(x_33);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_33);
lean_inc(x_33);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_33);
lean_inc(x_33);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_33);
lean_inc(x_33);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_33);
lean_inc(x_53);
lean_inc(x_50);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_50);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_53);
lean_inc(x_41);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_41);
lean_inc(x_41);
x_56 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_41);
lean_ctor_set(x_56, 2, x_15);
lean_ctor_set(x_56, 3, x_15);
lean_ctor_set_usize(x_56, 4, x_36);
lean_inc(x_33);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_33);
lean_inc_n(x_43, 2);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_43);
lean_ctor_set(x_58, 2, x_43);
lean_ctor_set(x_58, 3, x_57);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set(x_59, 2, x_32);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_58);
x_60 = lean_st_mk_ref(x_59, x_14);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_nat_sub(x_7, x_29);
lean_dec(x_29);
lean_inc(x_63);
x_64 = l___private_Init_GetElem_0__List_get_x21Internal___redArg(x_30, x_31, x_63);
x_65 = lean_box(1);
x_66 = lean_box(0);
x_67 = lean_box(2);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_33);
x_69 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_69, 0, x_42);
lean_ctor_set(x_69, 1, x_41);
lean_ctor_set(x_69, 2, x_15);
lean_ctor_set(x_69, 3, x_15);
lean_ctor_set_usize(x_69, 4, x_36);
x_70 = l_instInhabitedNat;
x_71 = lean_ctor_get(x_1, 5);
lean_inc(x_71);
x_72 = lean_box(x_16);
x_73 = lean_box(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_74 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___lam__0___boxed), 12, 5);
lean_closure_set(x_74, 0, x_64);
lean_closure_set(x_74, 1, x_3);
lean_closure_set(x_74, 2, x_1);
lean_closure_set(x_74, 3, x_72);
lean_closure_set(x_74, 4, x_73);
x_75 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_75, 0, x_16);
lean_ctor_set_uint8(x_75, 1, x_16);
lean_ctor_set_uint8(x_75, 2, x_16);
lean_ctor_set_uint8(x_75, 3, x_16);
lean_ctor_set_uint8(x_75, 4, x_16);
lean_ctor_set_uint8(x_75, 5, x_4);
lean_ctor_set_uint8(x_75, 6, x_4);
lean_ctor_set_uint8(x_75, 7, x_16);
lean_ctor_set_uint8(x_75, 8, x_4);
x_76 = lean_unbox(x_65);
lean_ctor_set_uint8(x_75, 9, x_76);
x_77 = lean_unbox(x_66);
lean_ctor_set_uint8(x_75, 10, x_77);
lean_ctor_set_uint8(x_75, 11, x_4);
lean_ctor_set_uint8(x_75, 12, x_4);
lean_ctor_set_uint8(x_75, 13, x_4);
x_78 = lean_unbox(x_67);
lean_ctor_set_uint8(x_75, 14, x_78);
lean_ctor_set_uint8(x_75, 15, x_4);
lean_ctor_set_uint8(x_75, 16, x_4);
lean_ctor_set_uint8(x_75, 17, x_4);
x_79 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_75);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_69);
lean_ctor_set(x_80, 2, x_32);
x_81 = lean_mk_empty_array_with_capacity(x_15);
x_82 = lean_box(0);
x_83 = lean_box(0);
x_84 = lean_array_get(x_70, x_71, x_63);
lean_dec(x_63);
lean_dec(x_71);
x_85 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_32);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set(x_85, 3, x_81);
lean_ctor_set(x_85, 4, x_82);
lean_ctor_set(x_85, 5, x_15);
lean_ctor_set(x_85, 6, x_83);
lean_ctor_set_uint64(x_85, sizeof(void*)*7, x_79);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 8, x_16);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 9, x_16);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 10, x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_61);
x_86 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg(x_26, x_84, x_74, x_16, x_85, x_61, x_12, x_13, x_62);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_st_ref_get(x_61, x_88);
lean_dec(x_61);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_20 = x_87;
x_21 = x_90;
goto block_25;
}
else
{
lean_dec(x_61);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_dec(x_86);
x_20 = x_91;
x_21 = x_92;
goto block_25;
}
else
{
uint8_t x_93; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_86);
if (x_93 == 0)
{
return x_86;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_86, 0);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_86);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_12 = l_instMonadEIO(lean_box(0));
x_13 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
lean_inc(x_27);
lean_inc(x_24);
lean_inc(x_21);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
x_30 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_24);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_27);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
x_44 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_43);
x_45 = lean_box(0);
x_46 = l_instInhabitedOfMonad___redArg(x_44, x_45);
x_47 = lean_panic_fn(x_46, x_1);
x_48 = lean_apply_6(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
return x_48;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_array_get(x_10, x_3, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = l_Lean_Name_getPrefix(x_13);
lean_dec(x_13);
x_15 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_14, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(1);
x_20 = lean_array_get_size(x_3);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_20);
x_23 = lean_unbox(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_24 = l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___redArg(x_1, x_18, x_3, x_23, x_3, x_20, x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_16);
lean_dec(x_1);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_34 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCasesImplementedBy", 56, 56);
x_35 = lean_unsigned_to_nat(576u);
x_36 = lean_unsigned_to_nat(55u);
x_37 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_38 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_33, x_34, x_35, x_36, x_37);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_39 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__7(x_38, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_1);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
lean_inc(x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_15);
lean_inc(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
lean_inc(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_15);
lean_inc(x_16);
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set(x_22, 7, x_20);
lean_ctor_set(x_22, 8, x_21);
lean_inc(x_15);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_15);
lean_inc(x_15);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_15);
lean_inc(x_15);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_15);
lean_inc(x_15);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_15);
lean_inc(x_26);
lean_inc(x_23);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_26);
x_28 = lean_unsigned_to_nat(5u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_nat_pow(x_1, x_30);
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
lean_ctor_set(x_36, 2, x_14);
lean_ctor_set(x_36, 3, x_14);
lean_ctor_set_usize(x_36, 4, x_29);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_15);
lean_inc_n(x_16, 2);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_16);
lean_ctor_set(x_38, 2, x_16);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_13);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_st_mk_ref(x_39, x_12);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(1);
x_44 = lean_box(1);
x_45 = lean_box(0);
x_46 = lean_box(2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 0, 18);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 0, x_49);
x_50 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 1, x_50);
x_51 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 2, x_51);
x_52 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 3, x_52);
x_53 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 4, x_53);
x_54 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 5, x_54);
x_55 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 6, x_55);
x_56 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 7, x_56);
x_57 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 8, x_57);
x_58 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 9, x_58);
x_59 = lean_unbox(x_45);
lean_ctor_set_uint8(x_48, 10, x_59);
x_60 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 11, x_60);
x_61 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 12, x_61);
x_62 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 13, x_62);
x_63 = lean_unbox(x_46);
lean_ctor_set_uint8(x_48, 14, x_63);
x_64 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 15, x_64);
x_65 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 16, x_65);
x_66 = lean_unbox(x_43);
lean_ctor_set_uint8(x_48, 17, x_66);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_48);
x_68 = lean_ctor_get(x_11, 0);
lean_inc(x_68);
lean_dec(x_11);
x_69 = lean_mk_empty_array_with_capacity(x_14);
x_70 = lean_box(0);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_13);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_69);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_14);
lean_ctor_set(x_72, 6, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*7, x_67);
x_73 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 8, x_73);
x_74 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 9, x_74);
x_75 = lean_unbox(x_47);
lean_ctor_set_uint8(x_72, sizeof(void*)*7 + 10, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_41);
x_76 = lean_infer_type(x_2, x_72, x_41, x_7, x_8, x_42);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_st_ref_get(x_41, x_78);
lean_dec(x_41);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_apply_7(x_3, x_77, x_4, x_5, x_6, x_7, x_8, x_80);
return x_81;
}
else
{
lean_dec(x_41);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_apply_7(x_3, x_82, x_4, x_5, x_6, x_7, x_8, x_83);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_76);
if (x_85 == 0)
{
return x_76;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_76, 0);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_76);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0___boxed), 7, 0);
x_9 = lean_unsigned_to_nat(2u);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1___boxed), 9, 3);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_unsigned_to_nat(5u);
x_11 = lean_box(0);
x_12 = l_Lean_Expr_sort___override(x_11);
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_13);
x_14 = lean_mk_array(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_13, x_15);
lean_dec(x_13);
lean_inc(x_1);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_9, x_17, x_18);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_19);
x_21 = lean_array_get(x_9, x_17, x_15);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_21);
x_23 = lean_array_get(x_9, x_17, x_2);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_mk_empty_array_with_capacity(x_24);
x_26 = lean_array_push(x_25, x_20);
x_27 = lean_array_push(x_26, x_22);
x_28 = l_Lean_Expr_beta(x_23, x_27);
x_29 = lean_array_get_size(x_17);
x_30 = l_Array_toSubarray___redArg(x_17, x_10, x_29);
x_31 = l_Array_ofSubarray___redArg(x_30);
lean_dec(x_30);
x_32 = l_Lean_mkAppN(x_28, x_31);
lean_dec(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_10, x_33, x_3, x_4, x_5, x_6, x_7, x_8);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_8 = lean_unsigned_to_nat(7u);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_sort___override(x_9);
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
lean_inc(x_1);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_12, x_14);
x_28 = lean_mk_string_unchecked("HEq", 3, 3);
x_29 = lean_mk_string_unchecked("rec", 3, 3);
lean_inc(x_28);
x_30 = l_Lean_Name_mkStr2(x_28, x_29);
x_31 = l_Lean_Expr_isAppOf(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_mk_string_unchecked("ndrec", 5, 5);
x_33 = l_Lean_Name_mkStr2(x_28, x_32);
x_34 = l_Lean_Expr_isAppOf(x_1, x_33);
lean_dec(x_33);
x_20 = x_34;
goto block_27;
}
else
{
lean_dec(x_28);
x_20 = x_31;
goto block_27;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed), 9, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_8);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_8, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
block_27:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_unsigned_to_nat(6u);
x_23 = lean_array_get(x_21, x_15, x_22);
x_16 = x_23;
goto block_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_instInhabitedExpr;
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_array_get(x_24, x_15, x_25);
x_16 = x_26;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_8 = lean_unsigned_to_nat(6u);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_sort___override(x_9);
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
lean_inc(x_1);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_12, x_14);
x_28 = lean_mk_string_unchecked("Eq", 2, 2);
x_29 = lean_mk_string_unchecked("rec", 3, 3);
lean_inc(x_28);
x_30 = l_Lean_Name_mkStr2(x_28, x_29);
x_31 = l_Lean_Expr_isAppOf(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_mk_string_unchecked("ndrec", 5, 5);
x_33 = l_Lean_Name_mkStr2(x_28, x_32);
x_34 = l_Lean_Expr_isAppOf(x_1, x_33);
lean_dec(x_33);
x_20 = x_34;
goto block_27;
}
else
{
lean_dec(x_28);
x_20 = x_31;
goto block_27;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed), 9, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_8);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_8, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
block_27:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_unsigned_to_nat(5u);
x_23 = lean_array_get(x_21, x_15, x_22);
x_16 = x_23;
goto block_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_instInhabitedExpr;
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_array_get(x_24, x_15, x_25);
x_16 = x_26;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_sort___override(x_10);
x_12 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
lean_inc(x_2);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_13, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst), 8, 2);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_9 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitQuotLift", 46, 46);
x_10 = lean_unsigned_to_nat(610u);
x_11 = lean_unsigned_to_nat(42u);
x_12 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_1, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(5u);
x_21 = lean_array_get(x_2, x_3, x_20);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_21, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Expr_getAppFn(x_4);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Expr_bvar___override(x_26);
x_28 = lean_apply_7(x_5, x_27, x_11, x_12, x_13, x_14, x_15, x_24);
return x_28;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Expr_fvar___override(x_29);
x_31 = lean_apply_7(x_5, x_30, x_11, x_12, x_13, x_14, x_15, x_24);
return x_31;
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l_Lean_Expr_mvar___override(x_32);
x_34 = lean_apply_7(x_5, x_33, x_11, x_12, x_13, x_14, x_15, x_24);
return x_34;
}
case 3:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = l_Lean_Expr_sort___override(x_35);
x_37 = lean_apply_7(x_5, x_36, x_11, x_12, x_13, x_14, x_15, x_24);
return x_37;
}
case 4:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = l_Lean_Expr_const___override(x_39, x_38);
x_41 = lean_apply_7(x_5, x_40, x_11, x_12, x_13, x_14, x_15, x_24);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
lean_dec(x_25);
x_44 = l_Lean_Expr_const___override(x_43, x_38);
x_45 = lean_apply_7(x_5, x_44, x_11, x_12, x_13, x_14, x_15, x_24);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_42, 1);
x_48 = lean_ctor_get(x_42, 0);
lean_dec(x_48);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_49; 
lean_dec(x_25);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_38);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_38, 1);
lean_dec(x_51);
x_52 = lean_mk_string_unchecked("Quot", 4, 4);
x_53 = lean_mk_string_unchecked("lcInv", 5, 5);
x_54 = l_Lean_Name_mkStr2(x_52, x_53);
lean_ctor_set(x_42, 0, x_50);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_6);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_7);
x_57 = lean_mk_empty_array_with_capacity(x_8);
x_58 = lean_array_push(x_57, x_55);
x_59 = lean_array_push(x_58, x_56);
x_60 = lean_array_push(x_59, x_23);
x_61 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_mk_string_unchecked("_x", 2, 2);
x_63 = l_Lean_Name_mkStr1(x_62);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_63);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_61, x_63, x_11, x_12, x_13, x_14, x_15, x_24);
if (lean_obj_tag(x_64) == 0)
{
switch (lean_obj_tag(x_18)) {
case 0:
{
uint8_t x_65; 
lean_dec(x_63);
lean_free_object(x_38);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_18);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_18);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
case 1:
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = !lean_is_exclusive(x_18);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_18, 0, x_69);
x_73 = lean_mk_empty_array_with_capacity(x_9);
x_74 = lean_array_push(x_73, x_18);
lean_ctor_set_tag(x_38, 4);
lean_ctor_set(x_38, 1, x_74);
lean_ctor_set(x_38, 0, x_72);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_38, x_63, x_11, x_12, x_13, x_14, x_15, x_70);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_76, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_77);
return x_78;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_75;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_18, 0);
lean_inc(x_79);
lean_dec(x_18);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_69);
x_81 = lean_mk_empty_array_with_capacity(x_9);
x_82 = lean_array_push(x_81, x_80);
lean_ctor_set_tag(x_38, 4);
lean_ctor_set(x_38, 1, x_82);
lean_ctor_set(x_38, 0, x_79);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_38, x_63, x_11, x_12, x_13, x_14, x_15, x_70);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_84, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_85);
return x_86;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_83;
}
}
}
default: 
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_63);
lean_free_object(x_38);
lean_dec(x_18);
lean_dec(x_10);
x_87 = lean_ctor_get(x_64, 1);
lean_inc(x_87);
lean_dec(x_64);
x_88 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_89 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitQuotLift", 46, 46);
x_90 = lean_unsigned_to_nat(614u);
x_91 = lean_unsigned_to_nat(19u);
x_92 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_93 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_88, x_89, x_90, x_91, x_92);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_88);
x_94 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_93, x_11, x_12, x_13, x_14, x_15, x_87);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_63);
lean_free_object(x_38);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_95 = !lean_is_exclusive(x_64);
if (x_95 == 0)
{
return x_64;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_64, 0);
x_97 = lean_ctor_get(x_64, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_64);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_99 = lean_ctor_get(x_38, 0);
lean_inc(x_99);
lean_dec(x_38);
x_100 = lean_mk_string_unchecked("Quot", 4, 4);
x_101 = lean_mk_string_unchecked("lcInv", 5, 5);
x_102 = l_Lean_Name_mkStr2(x_100, x_101);
lean_ctor_set(x_42, 0, x_99);
x_103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_103, 0, x_6);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_7);
x_105 = lean_mk_empty_array_with_capacity(x_8);
x_106 = lean_array_push(x_105, x_103);
x_107 = lean_array_push(x_106, x_104);
x_108 = lean_array_push(x_107, x_23);
x_109 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_42);
lean_ctor_set(x_109, 2, x_108);
x_110 = lean_mk_string_unchecked("_x", 2, 2);
x_111 = l_Lean_Name_mkStr1(x_110);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_111);
x_112 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_109, x_111, x_11, x_12, x_13, x_14, x_15, x_24);
if (lean_obj_tag(x_112) == 0)
{
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_111);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_18);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
case 1:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_ctor_get(x_18, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_119 = x_18;
} else {
 lean_dec_ref(x_18);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_116);
x_121 = lean_mk_empty_array_with_capacity(x_9);
x_122 = lean_array_push(x_121, x_120);
x_123 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_122);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_124 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_123, x_111, x_11, x_12, x_13, x_14, x_15, x_117);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_125, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_126);
return x_127;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_124;
}
}
default: 
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_111);
lean_dec(x_18);
lean_dec(x_10);
x_128 = lean_ctor_get(x_112, 1);
lean_inc(x_128);
lean_dec(x_112);
x_129 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_130 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitQuotLift", 46, 46);
x_131 = lean_unsigned_to_nat(614u);
x_132 = lean_unsigned_to_nat(19u);
x_133 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_134 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_129, x_130, x_131, x_132, x_133);
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_129);
x_135 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_134, x_11, x_12, x_13, x_14, x_15, x_128);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_111);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_136 = lean_ctor_get(x_112, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_112, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_138 = x_112;
} else {
 lean_dec_ref(x_112);
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
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_free_object(x_42);
lean_dec(x_47);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_140 = lean_ctor_get(x_25, 0);
lean_inc(x_140);
lean_dec(x_25);
x_141 = l_Lean_Expr_const___override(x_140, x_38);
x_142 = lean_apply_7(x_5, x_141, x_11, x_12, x_13, x_14, x_15, x_24);
return x_142;
}
}
else
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_42, 1);
lean_inc(x_143);
lean_dec(x_42);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_25);
lean_dec(x_5);
x_144 = lean_ctor_get(x_38, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_145 = x_38;
} else {
 lean_dec_ref(x_38);
 x_145 = lean_box(0);
}
x_146 = lean_mk_string_unchecked("Quot", 4, 4);
x_147 = lean_mk_string_unchecked("lcInv", 5, 5);
x_148 = l_Lean_Name_mkStr2(x_146, x_147);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_144);
lean_ctor_set(x_149, 1, x_143);
x_150 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_150, 0, x_6);
x_151 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_151, 0, x_7);
x_152 = lean_mk_empty_array_with_capacity(x_8);
x_153 = lean_array_push(x_152, x_150);
x_154 = lean_array_push(x_153, x_151);
x_155 = lean_array_push(x_154, x_23);
x_156 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_156, 0, x_148);
lean_ctor_set(x_156, 1, x_149);
lean_ctor_set(x_156, 2, x_155);
x_157 = lean_mk_string_unchecked("_x", 2, 2);
x_158 = l_Lean_Name_mkStr1(x_157);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_158);
x_159 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_156, x_158, x_11, x_12, x_13, x_14, x_15, x_24);
if (lean_obj_tag(x_159) == 0)
{
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_158);
lean_dec(x_145);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_18);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
case 1:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_dec(x_159);
x_165 = lean_ctor_get(x_18, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_166 = x_18;
} else {
 lean_dec_ref(x_18);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_163);
x_168 = lean_mk_empty_array_with_capacity(x_9);
x_169 = lean_array_push(x_168, x_167);
if (lean_is_scalar(x_145)) {
 x_170 = lean_alloc_ctor(4, 2, 0);
} else {
 x_170 = x_145;
 lean_ctor_set_tag(x_170, 4);
}
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_169);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_171 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_170, x_158, x_11, x_12, x_13, x_14, x_15, x_164);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_172, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_173);
return x_174;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_171;
}
}
default: 
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_158);
lean_dec(x_145);
lean_dec(x_18);
lean_dec(x_10);
x_175 = lean_ctor_get(x_159, 1);
lean_inc(x_175);
lean_dec(x_159);
x_176 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
x_177 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitQuotLift", 46, 46);
x_178 = lean_unsigned_to_nat(614u);
x_179 = lean_unsigned_to_nat(19u);
x_180 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_181 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_176, x_177, x_178, x_179, x_180);
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_176);
x_182 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_181, x_11, x_12, x_13, x_14, x_15, x_175);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_158);
lean_dec(x_145);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_183 = lean_ctor_get(x_159, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_159, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_185 = x_159;
} else {
 lean_dec_ref(x_159);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_143);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_187 = lean_ctor_get(x_25, 0);
lean_inc(x_187);
lean_dec(x_25);
x_188 = l_Lean_Expr_const___override(x_187, x_38);
x_189 = lean_apply_7(x_5, x_188, x_11, x_12, x_13, x_14, x_15, x_24);
return x_189;
}
}
}
}
}
case 5:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_190 = lean_ctor_get(x_25, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_25, 1);
lean_inc(x_191);
lean_dec(x_25);
x_192 = l_Lean_Expr_app___override(x_190, x_191);
x_193 = lean_apply_7(x_5, x_192, x_11, x_12, x_13, x_14, x_15, x_24);
return x_193;
}
case 6:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_194 = lean_ctor_get(x_25, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_25, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_25, 2);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
lean_dec(x_25);
x_198 = l_Lean_Expr_lam___override(x_194, x_195, x_196, x_197);
x_199 = lean_apply_7(x_5, x_198, x_11, x_12, x_13, x_14, x_15, x_24);
return x_199;
}
case 7:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_200 = lean_ctor_get(x_25, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_25, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_25, 2);
lean_inc(x_202);
x_203 = lean_ctor_get_uint8(x_25, sizeof(void*)*3 + 8);
lean_dec(x_25);
x_204 = l_Lean_Expr_forallE___override(x_200, x_201, x_202, x_203);
x_205 = lean_apply_7(x_5, x_204, x_11, x_12, x_13, x_14, x_15, x_24);
return x_205;
}
case 8:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_206 = lean_ctor_get(x_25, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_25, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_25, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_25, 3);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_25, sizeof(void*)*4 + 8);
lean_dec(x_25);
x_211 = l_Lean_Expr_letE___override(x_206, x_207, x_208, x_209, x_210);
x_212 = lean_apply_7(x_5, x_211, x_11, x_12, x_13, x_14, x_15, x_24);
return x_212;
}
case 9:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_213 = lean_ctor_get(x_25, 0);
lean_inc(x_213);
lean_dec(x_25);
x_214 = l_Lean_Expr_lit___override(x_213);
x_215 = lean_apply_7(x_5, x_214, x_11, x_12, x_13, x_14, x_15, x_24);
return x_215;
}
case 10:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_216 = lean_ctor_get(x_25, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_25, 1);
lean_inc(x_217);
lean_dec(x_25);
x_218 = l_Lean_Expr_mdata___override(x_216, x_217);
x_219 = lean_apply_7(x_5, x_218, x_11, x_12, x_13, x_14, x_15, x_24);
return x_219;
}
default: 
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_220 = lean_ctor_get(x_25, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_25, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_25, 2);
lean_inc(x_222);
lean_dec(x_25);
x_223 = l_Lean_Expr_proj___override(x_220, x_221, x_222);
x_224 = lean_apply_7(x_5, x_223, x_11, x_12, x_13, x_14, x_15, x_24);
return x_224;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed), 7, 0);
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_unsigned_to_nat(6u);
x_11 = lean_box(0);
x_12 = l_Lean_Expr_sort___override(x_11);
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_13);
x_14 = lean_mk_array(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_13, x_15);
lean_dec(x_13);
lean_inc(x_1);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_9, x_17, x_18);
x_20 = lean_array_get(x_9, x_17, x_15);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_array_get(x_9, x_17, x_21);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__1___boxed), 16, 10);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_9);
lean_closure_set(x_23, 2, x_17);
lean_closure_set(x_23, 3, x_1);
lean_closure_set(x_23, 4, x_8);
lean_closure_set(x_23, 5, x_19);
lean_closure_set(x_23, 6, x_20);
lean_closure_set(x_23, 7, x_21);
lean_closure_set(x_23, 8, x_15);
lean_closure_set(x_23, 9, x_10);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_10, x_23, x_2, x_3, x_4, x_5, x_6, x_7);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2_spec__2(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__2(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_lambdaBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__4(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___lam__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Array_mapFinIdxM_map___at___Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5_spec__5(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___redArg(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Array_mapFinIdxM_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCasesImplementedBy_spec__5(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_BorrowedAnnotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSimpAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
