// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Canon
// Imports: Init.Grind.Util Lean.Meta.Basic Lean.Meta.FunInfo Lean.Util.FVarSubset Lean.Util.PtrSet Lean.Util.FVarSubset Lean.Meta.Tactic.Grind.Types
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg(uint8_t, uint8_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___boxed(lean_object**);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImplicit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableNat___lam__0___boxed(lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult;
extern lean_object* l_Lean_instInhabitedExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___redArg___boxed(lean_object**);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___redArg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0(uint8_t, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___boxed(lean_object**);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashable;
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_mkAuxLemma_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___boxed(lean_object**);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
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
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
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
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
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
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 7);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*16);
x_17 = lean_ctor_get(x_5, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 10);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 11);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 12);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 13);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 14);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 15);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 2, x_10);
lean_ctor_set(x_25, 3, x_11);
lean_ctor_set(x_25, 4, x_12);
lean_ctor_set(x_25, 5, x_13);
lean_ctor_set(x_25, 6, x_14);
lean_ctor_set(x_25, 7, x_15);
lean_ctor_set(x_25, 8, x_17);
lean_ctor_set(x_25, 9, x_18);
lean_ctor_set(x_25, 10, x_19);
lean_ctor_set(x_25, 11, x_20);
lean_ctor_set(x_25, 12, x_21);
lean_ctor_set(x_25, 13, x_22);
lean_ctor_set(x_25, 14, x_23);
lean_ctor_set(x_25, 15, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*16, x_16);
x_26 = lean_st_ref_set(x_2, x_25, x_6);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
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
x_16 = lean_apply_1(x_1, x_15);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 7);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_12, sizeof(void*)*16);
x_24 = lean_ctor_get(x_12, 8);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 9);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 10);
lean_inc(x_26);
x_27 = lean_ctor_get(x_12, 11);
lean_inc(x_27);
x_28 = lean_ctor_get(x_12, 12);
lean_inc(x_28);
x_29 = lean_ctor_get(x_12, 13);
lean_inc(x_29);
x_30 = lean_ctor_get(x_12, 14);
lean_inc(x_30);
x_31 = lean_ctor_get(x_12, 15);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_16);
lean_ctor_set(x_32, 2, x_17);
lean_ctor_set(x_32, 3, x_18);
lean_ctor_set(x_32, 4, x_19);
lean_ctor_set(x_32, 5, x_20);
lean_ctor_set(x_32, 6, x_21);
lean_ctor_set(x_32, 7, x_22);
lean_ctor_set(x_32, 8, x_24);
lean_ctor_set(x_32, 9, x_25);
lean_ctor_set(x_32, 10, x_26);
lean_ctor_set(x_32, 11, x_27);
lean_ctor_set(x_32, 12, x_28);
lean_ctor_set(x_32, 13, x_29);
lean_ctor_set(x_32, 14, x_30);
lean_ctor_set(x_32, 15, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*16, x_23);
x_33 = lean_st_ref_set(x_2, x_32, x_13);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0), 10, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_7);
x_12 = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp___redArg(x_11, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
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
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; uint8_t x_107; uint64_t x_108; lean_object* x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint8_t x_113; uint64_t x_114; uint64_t x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_13 = l_Lean_Meta_Grind_getConfig___redArg(x_6, x_12);
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
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
lean_dec(x_14);
x_70 = lean_box(1);
x_71 = lean_ctor_get(x_10, 0);
x_72 = lean_ctor_get(x_10, 1);
x_73 = lean_ctor_get(x_10, 2);
x_74 = lean_ctor_get(x_10, 3);
x_75 = lean_ctor_get(x_10, 4);
x_76 = lean_ctor_get(x_10, 5);
x_77 = lean_ctor_get(x_10, 6);
x_78 = lean_ctor_get(x_10, 7);
x_79 = lean_ctor_get(x_10, 8);
x_80 = lean_unsigned_to_nat(1000u);
x_81 = lean_nat_mul(x_17, x_80);
x_82 = lean_ctor_get(x_10, 10);
x_83 = lean_ctor_get_uint8(x_10, sizeof(void*)*13);
x_84 = lean_ctor_get(x_10, 11);
x_85 = lean_ctor_get_uint8(x_10, sizeof(void*)*13 + 1);
x_86 = lean_ctor_get(x_10, 12);
lean_inc(x_86);
lean_inc(x_84);
lean_inc(x_82);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
x_87 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_87, 0, x_71);
lean_ctor_set(x_87, 1, x_72);
lean_ctor_set(x_87, 2, x_73);
lean_ctor_set(x_87, 3, x_74);
lean_ctor_set(x_87, 4, x_75);
lean_ctor_set(x_87, 5, x_76);
lean_ctor_set(x_87, 6, x_77);
lean_ctor_set(x_87, 7, x_78);
lean_ctor_set(x_87, 8, x_79);
lean_ctor_set(x_87, 9, x_81);
lean_ctor_set(x_87, 10, x_82);
lean_ctor_set(x_87, 11, x_84);
lean_ctor_set(x_87, 12, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*13, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*13 + 1, x_85);
x_88 = lean_ctor_get(x_8, 0);
x_89 = lean_ctor_get_uint8(x_88, 0);
x_90 = lean_ctor_get_uint8(x_88, 1);
x_91 = lean_ctor_get_uint8(x_88, 2);
x_92 = lean_ctor_get_uint8(x_88, 3);
x_93 = lean_ctor_get_uint8(x_88, 4);
x_94 = lean_ctor_get_uint8(x_88, 5);
x_95 = lean_ctor_get_uint8(x_88, 6);
x_96 = lean_ctor_get_uint8(x_88, 7);
x_97 = lean_ctor_get_uint8(x_88, 8);
x_98 = lean_ctor_get_uint8(x_88, 10);
x_99 = lean_ctor_get_uint8(x_88, 11);
x_100 = lean_ctor_get_uint8(x_88, 12);
x_101 = lean_ctor_get_uint8(x_88, 13);
x_102 = lean_ctor_get_uint8(x_88, 14);
x_103 = lean_ctor_get_uint8(x_88, 15);
x_104 = lean_ctor_get_uint8(x_88, 16);
x_105 = lean_ctor_get_uint8(x_88, 17);
x_106 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_106, 0, x_89);
lean_ctor_set_uint8(x_106, 1, x_90);
lean_ctor_set_uint8(x_106, 2, x_91);
lean_ctor_set_uint8(x_106, 3, x_92);
lean_ctor_set_uint8(x_106, 4, x_93);
lean_ctor_set_uint8(x_106, 5, x_94);
lean_ctor_set_uint8(x_106, 6, x_95);
lean_ctor_set_uint8(x_106, 7, x_96);
lean_ctor_set_uint8(x_106, 8, x_97);
x_107 = lean_unbox(x_70);
lean_ctor_set_uint8(x_106, 9, x_107);
lean_ctor_set_uint8(x_106, 10, x_98);
lean_ctor_set_uint8(x_106, 11, x_99);
lean_ctor_set_uint8(x_106, 12, x_100);
lean_ctor_set_uint8(x_106, 13, x_101);
lean_ctor_set_uint8(x_106, 14, x_102);
lean_ctor_set_uint8(x_106, 15, x_103);
lean_ctor_set_uint8(x_106, 16, x_104);
lean_ctor_set_uint8(x_106, 17, x_105);
x_108 = lean_ctor_get_uint64(x_8, sizeof(void*)*7);
x_109 = lean_unsigned_to_nat(2u);
x_110 = lean_uint64_of_nat(x_109);
x_111 = lean_uint64_shift_right(x_108, x_110);
x_112 = lean_uint64_shift_left(x_111, x_110);
x_113 = lean_unbox(x_70);
x_114 = l_Lean_Meta_TransparencyMode_toUInt64(x_113);
x_115 = lean_uint64_lor(x_112, x_114);
x_116 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_117 = lean_ctor_get(x_8, 1);
x_118 = lean_ctor_get(x_8, 2);
x_119 = lean_ctor_get(x_8, 3);
x_120 = lean_ctor_get(x_8, 4);
x_121 = lean_ctor_get(x_8, 5);
x_122 = lean_ctor_get(x_8, 6);
x_123 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_124 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
x_125 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_125, 0, x_106);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_125, 2, x_118);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set(x_125, 4, x_120);
lean_ctor_set(x_125, 5, x_121);
lean_ctor_set(x_125, 6, x_122);
lean_ctor_set_uint64(x_125, sizeof(void*)*7, x_115);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 8, x_116);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 9, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 10, x_124);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_126 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_125, x_9, x_87, x_11, x_15);
lean_dec(x_125);
if (lean_obj_tag(x_126) == 0)
{
if (lean_obj_tag(x_126) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_18 = x_127;
x_19 = x_128;
goto block_69;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
lean_dec(x_126);
x_18 = x_129;
x_19 = x_130;
goto block_69;
}
block_69:
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_16;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_16);
x_23 = l_Lean_Meta_Grind_getConfig___redArg(x_6, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*7 + 10);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(x_20);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_mk_string_unchecked("failed to show that", 19, 19);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = l_Lean_indentExpr(x_1);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("\nis definitionally equal to", 27, 27);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_indentExpr(x_2);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_mk_string_unchecked("\nwhile canonicalizing", 21, 21);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_indentExpr(x_3);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("\nusing `", 8, 8);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Init_Data_Repr_0__Nat_reprFast(x_17);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_MessageData_ofFormat(x_51);
lean_inc(x_52);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("*1000` heartbeats, `(canonHeartbeats := ", 40, 40);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
x_58 = lean_mk_string_unchecked(")`", 2, 2);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Meta_Grind_reportIssue(x_60, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_11);
lean_dec(x_9);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
x_64 = lean_box(x_20);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_box(x_20);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
else
{
lean_object* x_68; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_16)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_16;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_18);
lean_ctor_set(x_68, 1, x_19);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___boxed), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
x_14 = l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Core_withCurrHeartbeats___at_____private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_4 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
x_8 = l_instBEqOfDecidableEq___redArg(x_4);
x_9 = l_Lean_Expr_instHashable;
x_10 = lean_alloc_closure((void*)(l_instHashableNat___lam__0___boxed), 1, 0);
x_11 = l_instBEqProd___redArg(x_7, x_8);
x_12 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Expr_hash(x_5);
lean_dec(x_5);
x_14 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_11, x_12, x_1, x_16, x_18, x_2, x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; uint64_t x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint8_t x_50; uint64_t x_51; uint64_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_7);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_24 = lean_box(1);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_25, 0);
x_27 = lean_ctor_get_uint8(x_25, 1);
x_28 = lean_ctor_get_uint8(x_25, 2);
x_29 = lean_ctor_get_uint8(x_25, 3);
x_30 = lean_ctor_get_uint8(x_25, 4);
x_31 = lean_ctor_get_uint8(x_25, 5);
x_32 = lean_ctor_get_uint8(x_25, 6);
x_33 = lean_ctor_get_uint8(x_25, 7);
x_34 = lean_ctor_get_uint8(x_25, 8);
x_35 = lean_ctor_get_uint8(x_25, 10);
x_36 = lean_ctor_get_uint8(x_25, 11);
x_37 = lean_ctor_get_uint8(x_25, 12);
x_38 = lean_ctor_get_uint8(x_25, 13);
x_39 = lean_ctor_get_uint8(x_25, 14);
x_40 = lean_ctor_get_uint8(x_25, 15);
x_41 = lean_ctor_get_uint8(x_25, 16);
x_42 = lean_ctor_get_uint8(x_25, 17);
lean_dec(x_25);
x_43 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_43, 0, x_26);
lean_ctor_set_uint8(x_43, 1, x_27);
lean_ctor_set_uint8(x_43, 2, x_28);
lean_ctor_set_uint8(x_43, 3, x_29);
lean_ctor_set_uint8(x_43, 4, x_30);
lean_ctor_set_uint8(x_43, 5, x_31);
lean_ctor_set_uint8(x_43, 6, x_32);
lean_ctor_set_uint8(x_43, 7, x_33);
lean_ctor_set_uint8(x_43, 8, x_34);
x_44 = lean_unbox(x_24);
lean_ctor_set_uint8(x_43, 9, x_44);
lean_ctor_set_uint8(x_43, 10, x_35);
lean_ctor_set_uint8(x_43, 11, x_36);
lean_ctor_set_uint8(x_43, 12, x_37);
lean_ctor_set_uint8(x_43, 13, x_38);
lean_ctor_set_uint8(x_43, 14, x_39);
lean_ctor_set_uint8(x_43, 15, x_40);
lean_ctor_set_uint8(x_43, 16, x_41);
lean_ctor_set_uint8(x_43, 17, x_42);
x_45 = lean_ctor_get_uint64(x_12, sizeof(void*)*7);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_uint64_of_nat(x_46);
x_48 = lean_uint64_shift_right(x_45, x_47);
x_49 = lean_uint64_shift_left(x_48, x_47);
x_50 = lean_unbox(x_24);
x_51 = l_Lean_Meta_TransparencyMode_toUInt64(x_50);
x_52 = lean_uint64_lor(x_49, x_51);
x_53 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 8);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_12, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_12, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_12, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_12, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_12, 6);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 9);
x_61 = lean_ctor_get_uint8(x_12, sizeof(void*)*7 + 10);
x_62 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
lean_ctor_set(x_62, 6, x_59);
lean_ctor_set_uint64(x_62, sizeof(void*)*7, x_52);
lean_ctor_set_uint8(x_62, sizeof(void*)*7 + 8, x_53);
lean_ctor_set_uint8(x_62, sizeof(void*)*7 + 9, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*7 + 10, x_61);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
x_63 = l_Lean_Meta_isExprDefEq(x_1, x_22, x_62, x_13, x_14, x_15, x_16);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
lean_inc(x_2);
{
lean_object* _tmp_5 = x_19;
lean_object* _tmp_6 = x_2;
lean_object* _tmp_15 = x_66;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_16 = _tmp_15;
}
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_69 = x_63;
} else {
 lean_dec_ref(x_63);
 x_69 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_21);
lean_inc(x_3);
x_70 = l_Lean_Meta_isExprDefEq(x_3, x_21, x_12, x_13, x_14, x_15, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_80; uint8_t x_85; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
x_85 = lean_unbox(x_71);
lean_dec(x_71);
if (x_85 == 0)
{
lean_dec(x_73);
lean_dec(x_23);
if (x_4 == 0)
{
lean_dec(x_69);
lean_dec(x_21);
lean_dec(x_20);
lean_inc(x_2);
{
lean_object* _tmp_5 = x_19;
lean_object* _tmp_6 = x_2;
lean_object* _tmp_15 = x_72;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_16 = _tmp_15;
}
goto _start;
}
else
{
lean_object* x_87; 
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_21);
lean_inc(x_3);
x_87 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(x_3, x_21, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_72);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_69);
lean_dec(x_21);
lean_dec(x_20);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_2);
{
lean_object* _tmp_5 = x_19;
lean_object* _tmp_6 = x_2;
lean_object* _tmp_15 = x_90;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_16 = _tmp_15;
}
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_st_ref_take(x_8, x_92);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_inc(x_21);
lean_inc(x_3);
x_101 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_100, x_3, x_21);
x_102 = lean_ctor_get(x_98, 2);
lean_inc(x_102);
lean_dec(x_98);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_102);
x_104 = lean_ctor_get(x_95, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_95, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_95, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_95, 5);
lean_inc(x_107);
x_108 = lean_ctor_get(x_95, 6);
lean_inc(x_108);
x_109 = lean_ctor_get(x_95, 7);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_95, sizeof(void*)*16);
x_111 = lean_ctor_get(x_95, 8);
lean_inc(x_111);
x_112 = lean_ctor_get(x_95, 9);
lean_inc(x_112);
x_113 = lean_ctor_get(x_95, 10);
lean_inc(x_113);
x_114 = lean_ctor_get(x_95, 11);
lean_inc(x_114);
x_115 = lean_ctor_get(x_95, 12);
lean_inc(x_115);
x_116 = lean_ctor_get(x_95, 13);
lean_inc(x_116);
x_117 = lean_ctor_get(x_95, 14);
lean_inc(x_117);
x_118 = lean_ctor_get(x_95, 15);
lean_inc(x_118);
lean_dec(x_95);
x_119 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_119, 0, x_97);
lean_ctor_set(x_119, 1, x_103);
lean_ctor_set(x_119, 2, x_104);
lean_ctor_set(x_119, 3, x_105);
lean_ctor_set(x_119, 4, x_106);
lean_ctor_set(x_119, 5, x_107);
lean_ctor_set(x_119, 6, x_108);
lean_ctor_set(x_119, 7, x_109);
lean_ctor_set(x_119, 8, x_111);
lean_ctor_set(x_119, 9, x_112);
lean_ctor_set(x_119, 10, x_113);
lean_ctor_set(x_119, 11, x_114);
lean_ctor_set(x_119, 12, x_115);
lean_ctor_set(x_119, 13, x_116);
lean_ctor_set(x_119, 14, x_117);
lean_ctor_set(x_119, 15, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*16, x_110);
x_120 = lean_st_ref_set(x_8, x_119, x_96);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_122 = lean_ctor_get(x_120, 1);
x_123 = lean_ctor_get(x_120, 0);
lean_dec(x_123);
x_124 = lean_mk_string_unchecked("grind", 5, 5);
x_125 = lean_mk_string_unchecked("debugn", 6, 6);
x_126 = lean_mk_string_unchecked("canon", 5, 5);
x_127 = l_Lean_Name_mkStr3(x_124, x_125, x_126);
lean_inc(x_127);
x_128 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_127, x_14, x_122);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_127);
lean_free_object(x_120);
lean_free_object(x_93);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_80 = x_131;
goto block_84;
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_128);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_128, 1);
x_134 = lean_ctor_get(x_128, 0);
lean_dec(x_134);
x_135 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_133);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
x_139 = l_Lean_MessageData_ofExpr(x_3);
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_139);
lean_ctor_set(x_128, 0, x_138);
x_140 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_141 = l_Lean_stringToMessageData(x_140);
lean_dec(x_140);
lean_ctor_set_tag(x_120, 7);
lean_ctor_set(x_120, 1, x_141);
lean_ctor_set(x_120, 0, x_128);
lean_inc(x_21);
x_142 = l_Lean_MessageData_ofExpr(x_21);
lean_ctor_set_tag(x_93, 7);
lean_ctor_set(x_93, 1, x_142);
lean_ctor_set(x_93, 0, x_120);
x_143 = lean_mk_string_unchecked("", 0, 0);
x_144 = l_Lean_stringToMessageData(x_143);
lean_dec(x_143);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_93);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_127, x_145, x_12, x_13, x_14, x_15, x_136);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_80 = x_147;
goto block_84;
}
else
{
uint8_t x_148; 
lean_free_object(x_128);
lean_dec(x_127);
lean_free_object(x_120);
lean_free_object(x_93);
lean_dec(x_69);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_148 = !lean_is_exclusive(x_135);
if (x_148 == 0)
{
return x_135;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_135, 0);
x_150 = lean_ctor_get(x_135, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_135);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_128, 1);
lean_inc(x_152);
lean_dec(x_128);
x_153 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_152);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
x_156 = l_Lean_stringToMessageData(x_155);
lean_dec(x_155);
x_157 = l_Lean_MessageData_ofExpr(x_3);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
lean_ctor_set_tag(x_120, 7);
lean_ctor_set(x_120, 1, x_160);
lean_ctor_set(x_120, 0, x_158);
lean_inc(x_21);
x_161 = l_Lean_MessageData_ofExpr(x_21);
lean_ctor_set_tag(x_93, 7);
lean_ctor_set(x_93, 1, x_161);
lean_ctor_set(x_93, 0, x_120);
x_162 = lean_mk_string_unchecked("", 0, 0);
x_163 = l_Lean_stringToMessageData(x_162);
lean_dec(x_162);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_93);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_127, x_164, x_12, x_13, x_14, x_15, x_154);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_80 = x_166;
goto block_84;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_127);
lean_free_object(x_120);
lean_free_object(x_93);
lean_dec(x_69);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_167 = lean_ctor_get(x_153, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_153, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_169 = x_153;
} else {
 lean_dec_ref(x_153);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_171 = lean_ctor_get(x_120, 1);
lean_inc(x_171);
lean_dec(x_120);
x_172 = lean_mk_string_unchecked("grind", 5, 5);
x_173 = lean_mk_string_unchecked("debugn", 6, 6);
x_174 = lean_mk_string_unchecked("canon", 5, 5);
x_175 = l_Lean_Name_mkStr3(x_172, x_173, x_174);
lean_inc(x_175);
x_176 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_175, x_14, x_171);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_unbox(x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_175);
lean_free_object(x_93);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_80 = x_179;
goto block_84;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_176, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_181 = x_176;
} else {
 lean_dec_ref(x_176);
 x_181 = lean_box(0);
}
x_182 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_180);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
x_185 = l_Lean_stringToMessageData(x_184);
lean_dec(x_184);
x_186 = l_Lean_MessageData_ofExpr(x_3);
if (lean_is_scalar(x_181)) {
 x_187 = lean_alloc_ctor(7, 2, 0);
} else {
 x_187 = x_181;
 lean_ctor_set_tag(x_187, 7);
}
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_189 = l_Lean_stringToMessageData(x_188);
lean_dec(x_188);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_189);
lean_inc(x_21);
x_191 = l_Lean_MessageData_ofExpr(x_21);
lean_ctor_set_tag(x_93, 7);
lean_ctor_set(x_93, 1, x_191);
lean_ctor_set(x_93, 0, x_190);
x_192 = lean_mk_string_unchecked("", 0, 0);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_93);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_175, x_194, x_12, x_13, x_14, x_15, x_183);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_80 = x_196;
goto block_84;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_181);
lean_dec(x_175);
lean_free_object(x_93);
lean_dec(x_69);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_197 = lean_ctor_get(x_182, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_182, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_199 = x_182;
} else {
 lean_dec_ref(x_182);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_201 = lean_ctor_get(x_93, 0);
x_202 = lean_ctor_get(x_93, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_93);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_inc(x_21);
lean_inc(x_3);
x_207 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_206, x_3, x_21);
x_208 = lean_ctor_get(x_204, 2);
lean_inc(x_208);
lean_dec(x_204);
x_209 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_209, 0, x_205);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_209, 2, x_208);
x_210 = lean_ctor_get(x_201, 2);
lean_inc(x_210);
x_211 = lean_ctor_get(x_201, 3);
lean_inc(x_211);
x_212 = lean_ctor_get(x_201, 4);
lean_inc(x_212);
x_213 = lean_ctor_get(x_201, 5);
lean_inc(x_213);
x_214 = lean_ctor_get(x_201, 6);
lean_inc(x_214);
x_215 = lean_ctor_get(x_201, 7);
lean_inc(x_215);
x_216 = lean_ctor_get_uint8(x_201, sizeof(void*)*16);
x_217 = lean_ctor_get(x_201, 8);
lean_inc(x_217);
x_218 = lean_ctor_get(x_201, 9);
lean_inc(x_218);
x_219 = lean_ctor_get(x_201, 10);
lean_inc(x_219);
x_220 = lean_ctor_get(x_201, 11);
lean_inc(x_220);
x_221 = lean_ctor_get(x_201, 12);
lean_inc(x_221);
x_222 = lean_ctor_get(x_201, 13);
lean_inc(x_222);
x_223 = lean_ctor_get(x_201, 14);
lean_inc(x_223);
x_224 = lean_ctor_get(x_201, 15);
lean_inc(x_224);
lean_dec(x_201);
x_225 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_225, 0, x_203);
lean_ctor_set(x_225, 1, x_209);
lean_ctor_set(x_225, 2, x_210);
lean_ctor_set(x_225, 3, x_211);
lean_ctor_set(x_225, 4, x_212);
lean_ctor_set(x_225, 5, x_213);
lean_ctor_set(x_225, 6, x_214);
lean_ctor_set(x_225, 7, x_215);
lean_ctor_set(x_225, 8, x_217);
lean_ctor_set(x_225, 9, x_218);
lean_ctor_set(x_225, 10, x_219);
lean_ctor_set(x_225, 11, x_220);
lean_ctor_set(x_225, 12, x_221);
lean_ctor_set(x_225, 13, x_222);
lean_ctor_set(x_225, 14, x_223);
lean_ctor_set(x_225, 15, x_224);
lean_ctor_set_uint8(x_225, sizeof(void*)*16, x_216);
x_226 = lean_st_ref_set(x_8, x_225, x_202);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
x_229 = lean_mk_string_unchecked("grind", 5, 5);
x_230 = lean_mk_string_unchecked("debugn", 6, 6);
x_231 = lean_mk_string_unchecked("canon", 5, 5);
x_232 = l_Lean_Name_mkStr3(x_229, x_230, x_231);
lean_inc(x_232);
x_233 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_232, x_14, x_227);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_unbox(x_234);
lean_dec(x_234);
if (x_235 == 0)
{
lean_object* x_236; 
lean_dec(x_232);
lean_dec(x_228);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_80 = x_236;
goto block_84;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_238 = x_233;
} else {
 lean_dec_ref(x_233);
 x_238 = lean_box(0);
}
x_239 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_237);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
x_242 = l_Lean_stringToMessageData(x_241);
lean_dec(x_241);
x_243 = l_Lean_MessageData_ofExpr(x_3);
if (lean_is_scalar(x_238)) {
 x_244 = lean_alloc_ctor(7, 2, 0);
} else {
 x_244 = x_238;
 lean_ctor_set_tag(x_244, 7);
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_246 = l_Lean_stringToMessageData(x_245);
lean_dec(x_245);
if (lean_is_scalar(x_228)) {
 x_247 = lean_alloc_ctor(7, 2, 0);
} else {
 x_247 = x_228;
 lean_ctor_set_tag(x_247, 7);
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_246);
lean_inc(x_21);
x_248 = l_Lean_MessageData_ofExpr(x_21);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_mk_string_unchecked("", 0, 0);
x_251 = l_Lean_stringToMessageData(x_250);
lean_dec(x_250);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_232, x_252, x_12, x_13, x_14, x_15, x_240);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_80 = x_254;
goto block_84;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_238);
lean_dec(x_232);
lean_dec(x_228);
lean_dec(x_69);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_255 = lean_ctor_get(x_239, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_239, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_257 = x_239;
} else {
 lean_dec_ref(x_239);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_69);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = !lean_is_exclusive(x_87);
if (x_259 == 0)
{
return x_87;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_87, 0);
x_261 = lean_ctor_get(x_87, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_87);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
}
else
{
lean_object* x_263; uint8_t x_264; 
lean_dec(x_69);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_st_ref_take(x_8, x_72);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_ctor_get(x_263, 1);
x_267 = lean_ctor_get(x_265, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_265, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_inc(x_21);
lean_inc(x_3);
x_271 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_270, x_3, x_21);
x_272 = lean_ctor_get(x_268, 2);
lean_inc(x_272);
lean_dec(x_268);
x_273 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_273, 0, x_269);
lean_ctor_set(x_273, 1, x_271);
lean_ctor_set(x_273, 2, x_272);
x_274 = lean_ctor_get(x_265, 2);
lean_inc(x_274);
x_275 = lean_ctor_get(x_265, 3);
lean_inc(x_275);
x_276 = lean_ctor_get(x_265, 4);
lean_inc(x_276);
x_277 = lean_ctor_get(x_265, 5);
lean_inc(x_277);
x_278 = lean_ctor_get(x_265, 6);
lean_inc(x_278);
x_279 = lean_ctor_get(x_265, 7);
lean_inc(x_279);
x_280 = lean_ctor_get_uint8(x_265, sizeof(void*)*16);
x_281 = lean_ctor_get(x_265, 8);
lean_inc(x_281);
x_282 = lean_ctor_get(x_265, 9);
lean_inc(x_282);
x_283 = lean_ctor_get(x_265, 10);
lean_inc(x_283);
x_284 = lean_ctor_get(x_265, 11);
lean_inc(x_284);
x_285 = lean_ctor_get(x_265, 12);
lean_inc(x_285);
x_286 = lean_ctor_get(x_265, 13);
lean_inc(x_286);
x_287 = lean_ctor_get(x_265, 14);
lean_inc(x_287);
x_288 = lean_ctor_get(x_265, 15);
lean_inc(x_288);
lean_dec(x_265);
x_289 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_289, 0, x_267);
lean_ctor_set(x_289, 1, x_273);
lean_ctor_set(x_289, 2, x_274);
lean_ctor_set(x_289, 3, x_275);
lean_ctor_set(x_289, 4, x_276);
lean_ctor_set(x_289, 5, x_277);
lean_ctor_set(x_289, 6, x_278);
lean_ctor_set(x_289, 7, x_279);
lean_ctor_set(x_289, 8, x_281);
lean_ctor_set(x_289, 9, x_282);
lean_ctor_set(x_289, 10, x_283);
lean_ctor_set(x_289, 11, x_284);
lean_ctor_set(x_289, 12, x_285);
lean_ctor_set(x_289, 13, x_286);
lean_ctor_set(x_289, 14, x_287);
lean_ctor_set(x_289, 15, x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*16, x_280);
x_290 = lean_st_ref_set(x_8, x_289, x_266);
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_292 = lean_ctor_get(x_290, 1);
x_293 = lean_ctor_get(x_290, 0);
lean_dec(x_293);
x_294 = lean_mk_string_unchecked("grind", 5, 5);
x_295 = lean_mk_string_unchecked("debugn", 6, 6);
x_296 = lean_mk_string_unchecked("canon", 5, 5);
x_297 = l_Lean_Name_mkStr3(x_294, x_295, x_296);
lean_inc(x_297);
x_298 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_297, x_14, x_292);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_unbox(x_299);
lean_dec(x_299);
if (x_300 == 0)
{
lean_object* x_301; 
lean_dec(x_297);
lean_free_object(x_290);
lean_free_object(x_263);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_75 = x_301;
goto block_79;
}
else
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_298);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_298, 1);
x_304 = lean_ctor_get(x_298, 0);
lean_dec(x_304);
x_305 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_303);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_307 = lean_mk_string_unchecked("found ", 6, 6);
x_308 = l_Lean_stringToMessageData(x_307);
lean_dec(x_307);
x_309 = l_Lean_MessageData_ofExpr(x_3);
lean_ctor_set_tag(x_298, 7);
lean_ctor_set(x_298, 1, x_309);
lean_ctor_set(x_298, 0, x_308);
x_310 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_311 = l_Lean_stringToMessageData(x_310);
lean_dec(x_310);
lean_ctor_set_tag(x_290, 7);
lean_ctor_set(x_290, 1, x_311);
lean_ctor_set(x_290, 0, x_298);
lean_inc(x_21);
x_312 = l_Lean_MessageData_ofExpr(x_21);
lean_ctor_set_tag(x_263, 7);
lean_ctor_set(x_263, 1, x_312);
lean_ctor_set(x_263, 0, x_290);
x_313 = lean_mk_string_unchecked("", 0, 0);
x_314 = l_Lean_stringToMessageData(x_313);
lean_dec(x_313);
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_263);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_297, x_315, x_12, x_13, x_14, x_15, x_306);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_75 = x_317;
goto block_79;
}
else
{
uint8_t x_318; 
lean_free_object(x_298);
lean_dec(x_297);
lean_free_object(x_290);
lean_free_object(x_263);
lean_dec(x_73);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_318 = !lean_is_exclusive(x_305);
if (x_318 == 0)
{
return x_305;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_305, 0);
x_320 = lean_ctor_get(x_305, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_305);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_298, 1);
lean_inc(x_322);
lean_dec(x_298);
x_323 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_322);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
lean_dec(x_323);
x_325 = lean_mk_string_unchecked("found ", 6, 6);
x_326 = l_Lean_stringToMessageData(x_325);
lean_dec(x_325);
x_327 = l_Lean_MessageData_ofExpr(x_3);
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_330 = l_Lean_stringToMessageData(x_329);
lean_dec(x_329);
lean_ctor_set_tag(x_290, 7);
lean_ctor_set(x_290, 1, x_330);
lean_ctor_set(x_290, 0, x_328);
lean_inc(x_21);
x_331 = l_Lean_MessageData_ofExpr(x_21);
lean_ctor_set_tag(x_263, 7);
lean_ctor_set(x_263, 1, x_331);
lean_ctor_set(x_263, 0, x_290);
x_332 = lean_mk_string_unchecked("", 0, 0);
x_333 = l_Lean_stringToMessageData(x_332);
lean_dec(x_332);
x_334 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_334, 0, x_263);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_297, x_334, x_12, x_13, x_14, x_15, x_324);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
lean_dec(x_335);
x_75 = x_336;
goto block_79;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_297);
lean_free_object(x_290);
lean_free_object(x_263);
lean_dec(x_73);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_337 = lean_ctor_get(x_323, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_323, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_339 = x_323;
} else {
 lean_dec_ref(x_323);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_341 = lean_ctor_get(x_290, 1);
lean_inc(x_341);
lean_dec(x_290);
x_342 = lean_mk_string_unchecked("grind", 5, 5);
x_343 = lean_mk_string_unchecked("debugn", 6, 6);
x_344 = lean_mk_string_unchecked("canon", 5, 5);
x_345 = l_Lean_Name_mkStr3(x_342, x_343, x_344);
lean_inc(x_345);
x_346 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_345, x_14, x_341);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_unbox(x_347);
lean_dec(x_347);
if (x_348 == 0)
{
lean_object* x_349; 
lean_dec(x_345);
lean_free_object(x_263);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_dec(x_346);
x_75 = x_349;
goto block_79;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_346, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_351 = x_346;
} else {
 lean_dec_ref(x_346);
 x_351 = lean_box(0);
}
x_352 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_350);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
x_354 = lean_mk_string_unchecked("found ", 6, 6);
x_355 = l_Lean_stringToMessageData(x_354);
lean_dec(x_354);
x_356 = l_Lean_MessageData_ofExpr(x_3);
if (lean_is_scalar(x_351)) {
 x_357 = lean_alloc_ctor(7, 2, 0);
} else {
 x_357 = x_351;
 lean_ctor_set_tag(x_357, 7);
}
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_359 = l_Lean_stringToMessageData(x_358);
lean_dec(x_358);
x_360 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_359);
lean_inc(x_21);
x_361 = l_Lean_MessageData_ofExpr(x_21);
lean_ctor_set_tag(x_263, 7);
lean_ctor_set(x_263, 1, x_361);
lean_ctor_set(x_263, 0, x_360);
x_362 = lean_mk_string_unchecked("", 0, 0);
x_363 = l_Lean_stringToMessageData(x_362);
lean_dec(x_362);
x_364 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_364, 0, x_263);
lean_ctor_set(x_364, 1, x_363);
x_365 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_345, x_364, x_12, x_13, x_14, x_15, x_353);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
lean_dec(x_365);
x_75 = x_366;
goto block_79;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_351);
lean_dec(x_345);
lean_free_object(x_263);
lean_dec(x_73);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_367 = lean_ctor_get(x_352, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_352, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_369 = x_352;
} else {
 lean_dec_ref(x_352);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_371 = lean_ctor_get(x_263, 0);
x_372 = lean_ctor_get(x_263, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_263);
x_373 = lean_ctor_get(x_371, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_inc(x_21);
lean_inc(x_3);
x_377 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_376, x_3, x_21);
x_378 = lean_ctor_get(x_374, 2);
lean_inc(x_378);
lean_dec(x_374);
x_379 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_379, 0, x_375);
lean_ctor_set(x_379, 1, x_377);
lean_ctor_set(x_379, 2, x_378);
x_380 = lean_ctor_get(x_371, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_371, 3);
lean_inc(x_381);
x_382 = lean_ctor_get(x_371, 4);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 5);
lean_inc(x_383);
x_384 = lean_ctor_get(x_371, 6);
lean_inc(x_384);
x_385 = lean_ctor_get(x_371, 7);
lean_inc(x_385);
x_386 = lean_ctor_get_uint8(x_371, sizeof(void*)*16);
x_387 = lean_ctor_get(x_371, 8);
lean_inc(x_387);
x_388 = lean_ctor_get(x_371, 9);
lean_inc(x_388);
x_389 = lean_ctor_get(x_371, 10);
lean_inc(x_389);
x_390 = lean_ctor_get(x_371, 11);
lean_inc(x_390);
x_391 = lean_ctor_get(x_371, 12);
lean_inc(x_391);
x_392 = lean_ctor_get(x_371, 13);
lean_inc(x_392);
x_393 = lean_ctor_get(x_371, 14);
lean_inc(x_393);
x_394 = lean_ctor_get(x_371, 15);
lean_inc(x_394);
lean_dec(x_371);
x_395 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_395, 0, x_373);
lean_ctor_set(x_395, 1, x_379);
lean_ctor_set(x_395, 2, x_380);
lean_ctor_set(x_395, 3, x_381);
lean_ctor_set(x_395, 4, x_382);
lean_ctor_set(x_395, 5, x_383);
lean_ctor_set(x_395, 6, x_384);
lean_ctor_set(x_395, 7, x_385);
lean_ctor_set(x_395, 8, x_387);
lean_ctor_set(x_395, 9, x_388);
lean_ctor_set(x_395, 10, x_389);
lean_ctor_set(x_395, 11, x_390);
lean_ctor_set(x_395, 12, x_391);
lean_ctor_set(x_395, 13, x_392);
lean_ctor_set(x_395, 14, x_393);
lean_ctor_set(x_395, 15, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*16, x_386);
x_396 = lean_st_ref_set(x_8, x_395, x_372);
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
x_399 = lean_mk_string_unchecked("grind", 5, 5);
x_400 = lean_mk_string_unchecked("debugn", 6, 6);
x_401 = lean_mk_string_unchecked("canon", 5, 5);
x_402 = l_Lean_Name_mkStr3(x_399, x_400, x_401);
lean_inc(x_402);
x_403 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_402, x_14, x_397);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_unbox(x_404);
lean_dec(x_404);
if (x_405 == 0)
{
lean_object* x_406; 
lean_dec(x_402);
lean_dec(x_398);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
lean_dec(x_403);
x_75 = x_406;
goto block_79;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_403, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_408 = x_403;
} else {
 lean_dec_ref(x_403);
 x_408 = lean_box(0);
}
x_409 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_407);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
lean_dec(x_409);
x_411 = lean_mk_string_unchecked("found ", 6, 6);
x_412 = l_Lean_stringToMessageData(x_411);
lean_dec(x_411);
x_413 = l_Lean_MessageData_ofExpr(x_3);
if (lean_is_scalar(x_408)) {
 x_414 = lean_alloc_ctor(7, 2, 0);
} else {
 x_414 = x_408;
 lean_ctor_set_tag(x_414, 7);
}
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
x_415 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_416 = l_Lean_stringToMessageData(x_415);
lean_dec(x_415);
if (lean_is_scalar(x_398)) {
 x_417 = lean_alloc_ctor(7, 2, 0);
} else {
 x_417 = x_398;
 lean_ctor_set_tag(x_417, 7);
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_416);
lean_inc(x_21);
x_418 = l_Lean_MessageData_ofExpr(x_21);
x_419 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
x_420 = lean_mk_string_unchecked("", 0, 0);
x_421 = l_Lean_stringToMessageData(x_420);
lean_dec(x_420);
x_422 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_421);
x_423 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_402, x_422, x_12, x_13, x_14, x_15, x_410);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_75 = x_424;
goto block_79;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_408);
lean_dec(x_402);
lean_dec(x_398);
lean_dec(x_73);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_425 = lean_ctor_get(x_409, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_409, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_427 = x_409;
} else {
 lean_dec_ref(x_409);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
}
}
}
block_79:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_21);
if (lean_is_scalar(x_23)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_23;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
block_84:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_21);
if (lean_is_scalar(x_20)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_20;
 lean_ctor_set_tag(x_82, 0);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
if (lean_is_scalar(x_69)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_69;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
}
else
{
uint8_t x_429; 
lean_dec(x_69);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_429 = !lean_is_exclusive(x_70);
if (x_429 == 0)
{
return x_70;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_70, 0);
x_431 = lean_ctor_get(x_70, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_70);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_433 = !lean_is_exclusive(x_63);
if (x_433 == 0)
{
return x_63;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_63, 0);
x_435 = lean_ctor_get(x_63, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_63);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; uint64_t x_46; lean_object* x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint8_t x_51; uint64_t x_52; uint64_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = lean_box(1);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_26, 0);
x_28 = lean_ctor_get_uint8(x_26, 1);
x_29 = lean_ctor_get_uint8(x_26, 2);
x_30 = lean_ctor_get_uint8(x_26, 3);
x_31 = lean_ctor_get_uint8(x_26, 4);
x_32 = lean_ctor_get_uint8(x_26, 5);
x_33 = lean_ctor_get_uint8(x_26, 6);
x_34 = lean_ctor_get_uint8(x_26, 7);
x_35 = lean_ctor_get_uint8(x_26, 8);
x_36 = lean_ctor_get_uint8(x_26, 10);
x_37 = lean_ctor_get_uint8(x_26, 11);
x_38 = lean_ctor_get_uint8(x_26, 12);
x_39 = lean_ctor_get_uint8(x_26, 13);
x_40 = lean_ctor_get_uint8(x_26, 14);
x_41 = lean_ctor_get_uint8(x_26, 15);
x_42 = lean_ctor_get_uint8(x_26, 16);
x_43 = lean_ctor_get_uint8(x_26, 17);
lean_dec(x_26);
x_44 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_44, 0, x_27);
lean_ctor_set_uint8(x_44, 1, x_28);
lean_ctor_set_uint8(x_44, 2, x_29);
lean_ctor_set_uint8(x_44, 3, x_30);
lean_ctor_set_uint8(x_44, 4, x_31);
lean_ctor_set_uint8(x_44, 5, x_32);
lean_ctor_set_uint8(x_44, 6, x_33);
lean_ctor_set_uint8(x_44, 7, x_34);
lean_ctor_set_uint8(x_44, 8, x_35);
x_45 = lean_unbox(x_25);
lean_ctor_set_uint8(x_44, 9, x_45);
lean_ctor_set_uint8(x_44, 10, x_36);
lean_ctor_set_uint8(x_44, 11, x_37);
lean_ctor_set_uint8(x_44, 12, x_38);
lean_ctor_set_uint8(x_44, 13, x_39);
lean_ctor_set_uint8(x_44, 14, x_40);
lean_ctor_set_uint8(x_44, 15, x_41);
lean_ctor_set_uint8(x_44, 16, x_42);
lean_ctor_set_uint8(x_44, 17, x_43);
x_46 = lean_ctor_get_uint64(x_13, sizeof(void*)*7);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_uint64_of_nat(x_47);
x_49 = lean_uint64_shift_right(x_46, x_48);
x_50 = lean_uint64_shift_left(x_49, x_48);
x_51 = lean_unbox(x_25);
x_52 = l_Lean_Meta_TransparencyMode_toUInt64(x_51);
x_53 = lean_uint64_lor(x_50, x_52);
x_54 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 8);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_13, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_13, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_13, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_13, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_13, 6);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 9);
x_62 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 10);
x_63 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_63, 0, x_44);
lean_ctor_set(x_63, 1, x_55);
lean_ctor_set(x_63, 2, x_56);
lean_ctor_set(x_63, 3, x_57);
lean_ctor_set(x_63, 4, x_58);
lean_ctor_set(x_63, 5, x_59);
lean_ctor_set(x_63, 6, x_60);
lean_ctor_set_uint64(x_63, sizeof(void*)*7, x_53);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 8, x_54);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 9, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 10, x_62);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_1);
x_64 = l_Lean_Meta_isExprDefEq(x_1, x_23, x_63, x_14, x_15, x_16, x_17);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_2);
x_68 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_20, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_70 = x_64;
} else {
 lean_dec_ref(x_64);
 x_70 = lean_box(0);
}
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_22);
lean_inc(x_3);
x_71 = l_Lean_Meta_isExprDefEq(x_3, x_22, x_13, x_14, x_15, x_16, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_81; uint8_t x_86; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
x_86 = lean_unbox(x_72);
lean_dec(x_72);
if (x_86 == 0)
{
lean_dec(x_74);
lean_dec(x_24);
if (x_4 == 0)
{
lean_object* x_87; 
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_inc(x_2);
x_87 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_20, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_73);
return x_87;
}
else
{
lean_object* x_88; 
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_22);
lean_inc(x_3);
x_88 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(x_3, x_22, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_73);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
lean_inc(x_2);
x_92 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_20, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_dec(x_88);
x_94 = lean_st_ref_take(x_9, x_93);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_inc(x_22);
lean_inc(x_3);
x_102 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_101, x_3, x_22);
x_103 = lean_ctor_get(x_99, 2);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_103);
x_105 = lean_ctor_get(x_96, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_96, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_96, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_96, 5);
lean_inc(x_108);
x_109 = lean_ctor_get(x_96, 6);
lean_inc(x_109);
x_110 = lean_ctor_get(x_96, 7);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_96, sizeof(void*)*16);
x_112 = lean_ctor_get(x_96, 8);
lean_inc(x_112);
x_113 = lean_ctor_get(x_96, 9);
lean_inc(x_113);
x_114 = lean_ctor_get(x_96, 10);
lean_inc(x_114);
x_115 = lean_ctor_get(x_96, 11);
lean_inc(x_115);
x_116 = lean_ctor_get(x_96, 12);
lean_inc(x_116);
x_117 = lean_ctor_get(x_96, 13);
lean_inc(x_117);
x_118 = lean_ctor_get(x_96, 14);
lean_inc(x_118);
x_119 = lean_ctor_get(x_96, 15);
lean_inc(x_119);
lean_dec(x_96);
x_120 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_120, 0, x_98);
lean_ctor_set(x_120, 1, x_104);
lean_ctor_set(x_120, 2, x_105);
lean_ctor_set(x_120, 3, x_106);
lean_ctor_set(x_120, 4, x_107);
lean_ctor_set(x_120, 5, x_108);
lean_ctor_set(x_120, 6, x_109);
lean_ctor_set(x_120, 7, x_110);
lean_ctor_set(x_120, 8, x_112);
lean_ctor_set(x_120, 9, x_113);
lean_ctor_set(x_120, 10, x_114);
lean_ctor_set(x_120, 11, x_115);
lean_ctor_set(x_120, 12, x_116);
lean_ctor_set(x_120, 13, x_117);
lean_ctor_set(x_120, 14, x_118);
lean_ctor_set(x_120, 15, x_119);
lean_ctor_set_uint8(x_120, sizeof(void*)*16, x_111);
x_121 = lean_st_ref_set(x_9, x_120, x_97);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_123 = lean_ctor_get(x_121, 1);
x_124 = lean_ctor_get(x_121, 0);
lean_dec(x_124);
x_125 = lean_mk_string_unchecked("grind", 5, 5);
x_126 = lean_mk_string_unchecked("debugn", 6, 6);
x_127 = lean_mk_string_unchecked("canon", 5, 5);
x_128 = l_Lean_Name_mkStr3(x_125, x_126, x_127);
lean_inc(x_128);
x_129 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_128, x_15, x_123);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_128);
lean_free_object(x_121);
lean_free_object(x_94);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_81 = x_132;
goto block_85;
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_129);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_129, 1);
x_135 = lean_ctor_get(x_129, 0);
lean_dec(x_135);
x_136 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_134);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
x_139 = l_Lean_stringToMessageData(x_138);
lean_dec(x_138);
x_140 = l_Lean_MessageData_ofExpr(x_3);
lean_ctor_set_tag(x_129, 7);
lean_ctor_set(x_129, 1, x_140);
lean_ctor_set(x_129, 0, x_139);
x_141 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
lean_ctor_set_tag(x_121, 7);
lean_ctor_set(x_121, 1, x_142);
lean_ctor_set(x_121, 0, x_129);
lean_inc(x_22);
x_143 = l_Lean_MessageData_ofExpr(x_22);
lean_ctor_set_tag(x_94, 7);
lean_ctor_set(x_94, 1, x_143);
lean_ctor_set(x_94, 0, x_121);
x_144 = lean_mk_string_unchecked("", 0, 0);
x_145 = l_Lean_stringToMessageData(x_144);
lean_dec(x_144);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_94);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_128, x_146, x_13, x_14, x_15, x_16, x_137);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_81 = x_148;
goto block_85;
}
else
{
uint8_t x_149; 
lean_free_object(x_129);
lean_dec(x_128);
lean_free_object(x_121);
lean_free_object(x_94);
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_136);
if (x_149 == 0)
{
return x_136;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_136, 0);
x_151 = lean_ctor_get(x_136, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_136);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_129, 1);
lean_inc(x_153);
lean_dec(x_129);
x_154 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_153);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
x_157 = l_Lean_stringToMessageData(x_156);
lean_dec(x_156);
x_158 = l_Lean_MessageData_ofExpr(x_3);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_161 = l_Lean_stringToMessageData(x_160);
lean_dec(x_160);
lean_ctor_set_tag(x_121, 7);
lean_ctor_set(x_121, 1, x_161);
lean_ctor_set(x_121, 0, x_159);
lean_inc(x_22);
x_162 = l_Lean_MessageData_ofExpr(x_22);
lean_ctor_set_tag(x_94, 7);
lean_ctor_set(x_94, 1, x_162);
lean_ctor_set(x_94, 0, x_121);
x_163 = lean_mk_string_unchecked("", 0, 0);
x_164 = l_Lean_stringToMessageData(x_163);
lean_dec(x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_94);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_128, x_165, x_13, x_14, x_15, x_16, x_155);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_81 = x_167;
goto block_85;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_128);
lean_free_object(x_121);
lean_free_object(x_94);
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_168 = lean_ctor_get(x_154, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_154, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_170 = x_154;
} else {
 lean_dec_ref(x_154);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_172 = lean_ctor_get(x_121, 1);
lean_inc(x_172);
lean_dec(x_121);
x_173 = lean_mk_string_unchecked("grind", 5, 5);
x_174 = lean_mk_string_unchecked("debugn", 6, 6);
x_175 = lean_mk_string_unchecked("canon", 5, 5);
x_176 = l_Lean_Name_mkStr3(x_173, x_174, x_175);
lean_inc(x_176);
x_177 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_176, x_15, x_172);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec(x_176);
lean_free_object(x_94);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_81 = x_180;
goto block_85;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_182 = x_177;
} else {
 lean_dec_ref(x_177);
 x_182 = lean_box(0);
}
x_183 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_181);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
x_186 = l_Lean_stringToMessageData(x_185);
lean_dec(x_185);
x_187 = l_Lean_MessageData_ofExpr(x_3);
if (lean_is_scalar(x_182)) {
 x_188 = lean_alloc_ctor(7, 2, 0);
} else {
 x_188 = x_182;
 lean_ctor_set_tag(x_188, 7);
}
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_190 = l_Lean_stringToMessageData(x_189);
lean_dec(x_189);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
lean_inc(x_22);
x_192 = l_Lean_MessageData_ofExpr(x_22);
lean_ctor_set_tag(x_94, 7);
lean_ctor_set(x_94, 1, x_192);
lean_ctor_set(x_94, 0, x_191);
x_193 = lean_mk_string_unchecked("", 0, 0);
x_194 = l_Lean_stringToMessageData(x_193);
lean_dec(x_193);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_94);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_176, x_195, x_13, x_14, x_15, x_16, x_184);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_81 = x_197;
goto block_85;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_182);
lean_dec(x_176);
lean_free_object(x_94);
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_198 = lean_ctor_get(x_183, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_183, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_200 = x_183;
} else {
 lean_dec_ref(x_183);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_202 = lean_ctor_get(x_94, 0);
x_203 = lean_ctor_get(x_94, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_94);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_inc(x_22);
lean_inc(x_3);
x_208 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_207, x_3, x_22);
x_209 = lean_ctor_get(x_205, 2);
lean_inc(x_209);
lean_dec(x_205);
x_210 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_210, 0, x_206);
lean_ctor_set(x_210, 1, x_208);
lean_ctor_set(x_210, 2, x_209);
x_211 = lean_ctor_get(x_202, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_202, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_202, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_202, 5);
lean_inc(x_214);
x_215 = lean_ctor_get(x_202, 6);
lean_inc(x_215);
x_216 = lean_ctor_get(x_202, 7);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_202, sizeof(void*)*16);
x_218 = lean_ctor_get(x_202, 8);
lean_inc(x_218);
x_219 = lean_ctor_get(x_202, 9);
lean_inc(x_219);
x_220 = lean_ctor_get(x_202, 10);
lean_inc(x_220);
x_221 = lean_ctor_get(x_202, 11);
lean_inc(x_221);
x_222 = lean_ctor_get(x_202, 12);
lean_inc(x_222);
x_223 = lean_ctor_get(x_202, 13);
lean_inc(x_223);
x_224 = lean_ctor_get(x_202, 14);
lean_inc(x_224);
x_225 = lean_ctor_get(x_202, 15);
lean_inc(x_225);
lean_dec(x_202);
x_226 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_226, 0, x_204);
lean_ctor_set(x_226, 1, x_210);
lean_ctor_set(x_226, 2, x_211);
lean_ctor_set(x_226, 3, x_212);
lean_ctor_set(x_226, 4, x_213);
lean_ctor_set(x_226, 5, x_214);
lean_ctor_set(x_226, 6, x_215);
lean_ctor_set(x_226, 7, x_216);
lean_ctor_set(x_226, 8, x_218);
lean_ctor_set(x_226, 9, x_219);
lean_ctor_set(x_226, 10, x_220);
lean_ctor_set(x_226, 11, x_221);
lean_ctor_set(x_226, 12, x_222);
lean_ctor_set(x_226, 13, x_223);
lean_ctor_set(x_226, 14, x_224);
lean_ctor_set(x_226, 15, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*16, x_217);
x_227 = lean_st_ref_set(x_9, x_226, x_203);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
x_230 = lean_mk_string_unchecked("grind", 5, 5);
x_231 = lean_mk_string_unchecked("debugn", 6, 6);
x_232 = lean_mk_string_unchecked("canon", 5, 5);
x_233 = l_Lean_Name_mkStr3(x_230, x_231, x_232);
lean_inc(x_233);
x_234 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_233, x_15, x_228);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_233);
lean_dec(x_229);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_81 = x_237;
goto block_85;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_239 = x_234;
} else {
 lean_dec_ref(x_234);
 x_239 = lean_box(0);
}
x_240 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_238);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_mk_string_unchecked("found using `isDefEqBounded`: ", 30, 30);
x_243 = l_Lean_stringToMessageData(x_242);
lean_dec(x_242);
x_244 = l_Lean_MessageData_ofExpr(x_3);
if (lean_is_scalar(x_239)) {
 x_245 = lean_alloc_ctor(7, 2, 0);
} else {
 x_245 = x_239;
 lean_ctor_set_tag(x_245, 7);
}
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_247 = l_Lean_stringToMessageData(x_246);
lean_dec(x_246);
if (lean_is_scalar(x_229)) {
 x_248 = lean_alloc_ctor(7, 2, 0);
} else {
 x_248 = x_229;
 lean_ctor_set_tag(x_248, 7);
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_247);
lean_inc(x_22);
x_249 = l_Lean_MessageData_ofExpr(x_22);
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_mk_string_unchecked("", 0, 0);
x_252 = l_Lean_stringToMessageData(x_251);
lean_dec(x_251);
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_233, x_253, x_13, x_14, x_15, x_16, x_241);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_81 = x_255;
goto block_85;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_239);
lean_dec(x_233);
lean_dec(x_229);
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_256 = lean_ctor_get(x_240, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_240, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_258 = x_240;
} else {
 lean_dec_ref(x_240);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_70);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_88);
if (x_260 == 0)
{
return x_88;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_88, 0);
x_262 = lean_ctor_get(x_88, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_88);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
}
else
{
lean_object* x_264; uint8_t x_265; 
lean_dec(x_70);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_264 = lean_st_ref_take(x_9, x_73);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_ctor_get(x_264, 1);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_inc(x_22);
lean_inc(x_3);
x_272 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_271, x_3, x_22);
x_273 = lean_ctor_get(x_269, 2);
lean_inc(x_273);
lean_dec(x_269);
x_274 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_274, 0, x_270);
lean_ctor_set(x_274, 1, x_272);
lean_ctor_set(x_274, 2, x_273);
x_275 = lean_ctor_get(x_266, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_266, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_266, 4);
lean_inc(x_277);
x_278 = lean_ctor_get(x_266, 5);
lean_inc(x_278);
x_279 = lean_ctor_get(x_266, 6);
lean_inc(x_279);
x_280 = lean_ctor_get(x_266, 7);
lean_inc(x_280);
x_281 = lean_ctor_get_uint8(x_266, sizeof(void*)*16);
x_282 = lean_ctor_get(x_266, 8);
lean_inc(x_282);
x_283 = lean_ctor_get(x_266, 9);
lean_inc(x_283);
x_284 = lean_ctor_get(x_266, 10);
lean_inc(x_284);
x_285 = lean_ctor_get(x_266, 11);
lean_inc(x_285);
x_286 = lean_ctor_get(x_266, 12);
lean_inc(x_286);
x_287 = lean_ctor_get(x_266, 13);
lean_inc(x_287);
x_288 = lean_ctor_get(x_266, 14);
lean_inc(x_288);
x_289 = lean_ctor_get(x_266, 15);
lean_inc(x_289);
lean_dec(x_266);
x_290 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_290, 0, x_268);
lean_ctor_set(x_290, 1, x_274);
lean_ctor_set(x_290, 2, x_275);
lean_ctor_set(x_290, 3, x_276);
lean_ctor_set(x_290, 4, x_277);
lean_ctor_set(x_290, 5, x_278);
lean_ctor_set(x_290, 6, x_279);
lean_ctor_set(x_290, 7, x_280);
lean_ctor_set(x_290, 8, x_282);
lean_ctor_set(x_290, 9, x_283);
lean_ctor_set(x_290, 10, x_284);
lean_ctor_set(x_290, 11, x_285);
lean_ctor_set(x_290, 12, x_286);
lean_ctor_set(x_290, 13, x_287);
lean_ctor_set(x_290, 14, x_288);
lean_ctor_set(x_290, 15, x_289);
lean_ctor_set_uint8(x_290, sizeof(void*)*16, x_281);
x_291 = lean_st_ref_set(x_9, x_290, x_267);
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_293 = lean_ctor_get(x_291, 1);
x_294 = lean_ctor_get(x_291, 0);
lean_dec(x_294);
x_295 = lean_mk_string_unchecked("grind", 5, 5);
x_296 = lean_mk_string_unchecked("debugn", 6, 6);
x_297 = lean_mk_string_unchecked("canon", 5, 5);
x_298 = l_Lean_Name_mkStr3(x_295, x_296, x_297);
lean_inc(x_298);
x_299 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_298, x_15, x_293);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_unbox(x_300);
lean_dec(x_300);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_298);
lean_free_object(x_291);
lean_free_object(x_264);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_76 = x_302;
goto block_80;
}
else
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_299);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_299, 1);
x_305 = lean_ctor_get(x_299, 0);
lean_dec(x_305);
x_306 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_304);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_308 = lean_mk_string_unchecked("found ", 6, 6);
x_309 = l_Lean_stringToMessageData(x_308);
lean_dec(x_308);
x_310 = l_Lean_MessageData_ofExpr(x_3);
lean_ctor_set_tag(x_299, 7);
lean_ctor_set(x_299, 1, x_310);
lean_ctor_set(x_299, 0, x_309);
x_311 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_312 = l_Lean_stringToMessageData(x_311);
lean_dec(x_311);
lean_ctor_set_tag(x_291, 7);
lean_ctor_set(x_291, 1, x_312);
lean_ctor_set(x_291, 0, x_299);
lean_inc(x_22);
x_313 = l_Lean_MessageData_ofExpr(x_22);
lean_ctor_set_tag(x_264, 7);
lean_ctor_set(x_264, 1, x_313);
lean_ctor_set(x_264, 0, x_291);
x_314 = lean_mk_string_unchecked("", 0, 0);
x_315 = l_Lean_stringToMessageData(x_314);
lean_dec(x_314);
x_316 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_316, 0, x_264);
lean_ctor_set(x_316, 1, x_315);
x_317 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_298, x_316, x_13, x_14, x_15, x_16, x_307);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_76 = x_318;
goto block_80;
}
else
{
uint8_t x_319; 
lean_free_object(x_299);
lean_dec(x_298);
lean_free_object(x_291);
lean_free_object(x_264);
lean_dec(x_74);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_319 = !lean_is_exclusive(x_306);
if (x_319 == 0)
{
return x_306;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_306, 0);
x_321 = lean_ctor_get(x_306, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_306);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_299, 1);
lean_inc(x_323);
lean_dec(x_299);
x_324 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_323);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_mk_string_unchecked("found ", 6, 6);
x_327 = l_Lean_stringToMessageData(x_326);
lean_dec(x_326);
x_328 = l_Lean_MessageData_ofExpr(x_3);
x_329 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_331 = l_Lean_stringToMessageData(x_330);
lean_dec(x_330);
lean_ctor_set_tag(x_291, 7);
lean_ctor_set(x_291, 1, x_331);
lean_ctor_set(x_291, 0, x_329);
lean_inc(x_22);
x_332 = l_Lean_MessageData_ofExpr(x_22);
lean_ctor_set_tag(x_264, 7);
lean_ctor_set(x_264, 1, x_332);
lean_ctor_set(x_264, 0, x_291);
x_333 = lean_mk_string_unchecked("", 0, 0);
x_334 = l_Lean_stringToMessageData(x_333);
lean_dec(x_333);
x_335 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_335, 0, x_264);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_298, x_335, x_13, x_14, x_15, x_16, x_325);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
lean_dec(x_336);
x_76 = x_337;
goto block_80;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_298);
lean_free_object(x_291);
lean_free_object(x_264);
lean_dec(x_74);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_338 = lean_ctor_get(x_324, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_324, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_340 = x_324;
} else {
 lean_dec_ref(x_324);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_342 = lean_ctor_get(x_291, 1);
lean_inc(x_342);
lean_dec(x_291);
x_343 = lean_mk_string_unchecked("grind", 5, 5);
x_344 = lean_mk_string_unchecked("debugn", 6, 6);
x_345 = lean_mk_string_unchecked("canon", 5, 5);
x_346 = l_Lean_Name_mkStr3(x_343, x_344, x_345);
lean_inc(x_346);
x_347 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_346, x_15, x_342);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_unbox(x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; 
lean_dec(x_346);
lean_free_object(x_264);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_76 = x_350;
goto block_80;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_352 = x_347;
} else {
 lean_dec_ref(x_347);
 x_352 = lean_box(0);
}
x_353 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_351);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
lean_dec(x_353);
x_355 = lean_mk_string_unchecked("found ", 6, 6);
x_356 = l_Lean_stringToMessageData(x_355);
lean_dec(x_355);
x_357 = l_Lean_MessageData_ofExpr(x_3);
if (lean_is_scalar(x_352)) {
 x_358 = lean_alloc_ctor(7, 2, 0);
} else {
 x_358 = x_352;
 lean_ctor_set_tag(x_358, 7);
}
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_360 = l_Lean_stringToMessageData(x_359);
lean_dec(x_359);
x_361 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_360);
lean_inc(x_22);
x_362 = l_Lean_MessageData_ofExpr(x_22);
lean_ctor_set_tag(x_264, 7);
lean_ctor_set(x_264, 1, x_362);
lean_ctor_set(x_264, 0, x_361);
x_363 = lean_mk_string_unchecked("", 0, 0);
x_364 = l_Lean_stringToMessageData(x_363);
lean_dec(x_363);
x_365 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_365, 0, x_264);
lean_ctor_set(x_365, 1, x_364);
x_366 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_346, x_365, x_13, x_14, x_15, x_16, x_354);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
x_76 = x_367;
goto block_80;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_352);
lean_dec(x_346);
lean_free_object(x_264);
lean_dec(x_74);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_368 = lean_ctor_get(x_353, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_353, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_370 = x_353;
} else {
 lean_dec_ref(x_353);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_372 = lean_ctor_get(x_264, 0);
x_373 = lean_ctor_get(x_264, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_264);
x_374 = lean_ctor_get(x_372, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_inc(x_22);
lean_inc(x_3);
x_378 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_377, x_3, x_22);
x_379 = lean_ctor_get(x_375, 2);
lean_inc(x_379);
lean_dec(x_375);
x_380 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_380, 0, x_376);
lean_ctor_set(x_380, 1, x_378);
lean_ctor_set(x_380, 2, x_379);
x_381 = lean_ctor_get(x_372, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_372, 3);
lean_inc(x_382);
x_383 = lean_ctor_get(x_372, 4);
lean_inc(x_383);
x_384 = lean_ctor_get(x_372, 5);
lean_inc(x_384);
x_385 = lean_ctor_get(x_372, 6);
lean_inc(x_385);
x_386 = lean_ctor_get(x_372, 7);
lean_inc(x_386);
x_387 = lean_ctor_get_uint8(x_372, sizeof(void*)*16);
x_388 = lean_ctor_get(x_372, 8);
lean_inc(x_388);
x_389 = lean_ctor_get(x_372, 9);
lean_inc(x_389);
x_390 = lean_ctor_get(x_372, 10);
lean_inc(x_390);
x_391 = lean_ctor_get(x_372, 11);
lean_inc(x_391);
x_392 = lean_ctor_get(x_372, 12);
lean_inc(x_392);
x_393 = lean_ctor_get(x_372, 13);
lean_inc(x_393);
x_394 = lean_ctor_get(x_372, 14);
lean_inc(x_394);
x_395 = lean_ctor_get(x_372, 15);
lean_inc(x_395);
lean_dec(x_372);
x_396 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_396, 0, x_374);
lean_ctor_set(x_396, 1, x_380);
lean_ctor_set(x_396, 2, x_381);
lean_ctor_set(x_396, 3, x_382);
lean_ctor_set(x_396, 4, x_383);
lean_ctor_set(x_396, 5, x_384);
lean_ctor_set(x_396, 6, x_385);
lean_ctor_set(x_396, 7, x_386);
lean_ctor_set(x_396, 8, x_388);
lean_ctor_set(x_396, 9, x_389);
lean_ctor_set(x_396, 10, x_390);
lean_ctor_set(x_396, 11, x_391);
lean_ctor_set(x_396, 12, x_392);
lean_ctor_set(x_396, 13, x_393);
lean_ctor_set(x_396, 14, x_394);
lean_ctor_set(x_396, 15, x_395);
lean_ctor_set_uint8(x_396, sizeof(void*)*16, x_387);
x_397 = lean_st_ref_set(x_9, x_396, x_373);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_399 = x_397;
} else {
 lean_dec_ref(x_397);
 x_399 = lean_box(0);
}
x_400 = lean_mk_string_unchecked("grind", 5, 5);
x_401 = lean_mk_string_unchecked("debugn", 6, 6);
x_402 = lean_mk_string_unchecked("canon", 5, 5);
x_403 = l_Lean_Name_mkStr3(x_400, x_401, x_402);
lean_inc(x_403);
x_404 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_403, x_15, x_398);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_unbox(x_405);
lean_dec(x_405);
if (x_406 == 0)
{
lean_object* x_407; 
lean_dec(x_403);
lean_dec(x_399);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_407 = lean_ctor_get(x_404, 1);
lean_inc(x_407);
lean_dec(x_404);
x_76 = x_407;
goto block_80;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_409 = x_404;
} else {
 lean_dec_ref(x_404);
 x_409 = lean_box(0);
}
x_410 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_408);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_412 = lean_mk_string_unchecked("found ", 6, 6);
x_413 = l_Lean_stringToMessageData(x_412);
lean_dec(x_412);
x_414 = l_Lean_MessageData_ofExpr(x_3);
if (lean_is_scalar(x_409)) {
 x_415 = lean_alloc_ctor(7, 2, 0);
} else {
 x_415 = x_409;
 lean_ctor_set_tag(x_415, 7);
}
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_mk_string_unchecked(" ===> ", 6, 6);
x_417 = l_Lean_stringToMessageData(x_416);
lean_dec(x_416);
if (lean_is_scalar(x_399)) {
 x_418 = lean_alloc_ctor(7, 2, 0);
} else {
 x_418 = x_399;
 lean_ctor_set_tag(x_418, 7);
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_417);
lean_inc(x_22);
x_419 = l_Lean_MessageData_ofExpr(x_22);
x_420 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_mk_string_unchecked("", 0, 0);
x_422 = l_Lean_stringToMessageData(x_421);
lean_dec(x_421);
x_423 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_422);
x_424 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_403, x_423, x_13, x_14, x_15, x_16, x_411);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
lean_dec(x_424);
x_76 = x_425;
goto block_80;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_409);
lean_dec(x_403);
lean_dec(x_399);
lean_dec(x_74);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_426 = lean_ctor_get(x_410, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_410, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_428 = x_410;
} else {
 lean_dec_ref(x_410);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
}
}
block_80:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_22);
if (lean_is_scalar(x_24)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_24;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
block_85:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_22);
if (lean_is_scalar(x_21)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_21;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
if (lean_is_scalar(x_70)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_70;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
uint8_t x_430; 
lean_dec(x_70);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_430 = !lean_is_exclusive(x_71);
if (x_430 == 0)
{
return x_71;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_71, 0);
x_432 = lean_ctor_get(x_71, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_71);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_434 = !lean_is_exclusive(x_64);
if (x_434 == 0)
{
return x_64;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_64, 0);
x_436 = lean_ctor_get(x_64, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_64);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_array_fget(x_1, x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_expr_eqv(x_15, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_19);
x_5 = x_20;
goto block_11;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_eq(x_16, x_19);
lean_dec(x_19);
x_5 = x_21;
goto block_11;
}
}
block_11:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_6 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(5u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_shift_left(x_10, x_8);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get(x_6, x_4, x_14);
lean_dec(x_14);
lean_dec(x_4);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_expr_eqv(x_22, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_25);
x_18 = x_26;
goto block_21;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_23, x_25);
lean_dec(x_25);
x_18 = x_27;
goto block_21;
}
block_21:
{
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_5);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
if (lean_is_scalar(x_5)) {
 x_20 = lean_alloc_ctor(1, 1, 0);
} else {
 x_20 = x_5;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
}
}
case 1:
{
lean_object* x_28; size_t x_29; 
lean_dec(x_5);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_usize_shift_right(x_2, x_8);
x_1 = x_28;
x_2 = x_29;
goto _start;
}
default: 
{
lean_object* x_31; 
lean_dec(x_5);
x_31 = lean_box(0);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___redArg(x_32, x_33, x_34, x_3);
lean_dec(x_33);
lean_dec(x_32);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Expr_hash(x_3);
x_6 = lean_uint64_of_nat(x_4);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___redArg(x_1, x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_get(x_6, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_mkAuxLemma_spec__0___redArg(x_20, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_free_object(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_22 = lean_infer_type(x_4, x_10, x_11, x_12, x_13, x_18);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_96; lean_object* x_179; lean_object* x_180; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_3);
lean_inc(x_2);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 0, x_2);
x_179 = lean_ctor_get(x_19, 0);
lean_inc(x_179);
lean_dec(x_19);
x_180 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg(x_179, x_22);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_box(0);
x_96 = x_181;
goto block_178;
}
else
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_96 = x_182;
goto block_178;
}
block_95:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_st_ref_take(x_27, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_inc(x_4);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 0, x_4);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_26);
x_37 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(x_35, x_22, x_36);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_inc_n(x_4, 2);
x_39 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_38, x_4, x_4);
x_40 = lean_ctor_get(x_34, 2);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_ctor_get(x_31, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_31, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_31, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_31, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_31, 6);
lean_inc(x_46);
x_47 = lean_ctor_get(x_31, 7);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_31, sizeof(void*)*16);
x_49 = lean_ctor_get(x_31, 8);
lean_inc(x_49);
x_50 = lean_ctor_get(x_31, 9);
lean_inc(x_50);
x_51 = lean_ctor_get(x_31, 10);
lean_inc(x_51);
x_52 = lean_ctor_get(x_31, 11);
lean_inc(x_52);
x_53 = lean_ctor_get(x_31, 12);
lean_inc(x_53);
x_54 = lean_ctor_get(x_31, 13);
lean_inc(x_54);
x_55 = lean_ctor_get(x_31, 14);
lean_inc(x_55);
x_56 = lean_ctor_get(x_31, 15);
lean_inc(x_56);
lean_dec(x_31);
x_57 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_42);
lean_ctor_set(x_57, 3, x_43);
lean_ctor_set(x_57, 4, x_44);
lean_ctor_set(x_57, 5, x_45);
lean_ctor_set(x_57, 6, x_46);
lean_ctor_set(x_57, 7, x_47);
lean_ctor_set(x_57, 8, x_49);
lean_ctor_set(x_57, 9, x_50);
lean_ctor_set(x_57, 10, x_51);
lean_ctor_set(x_57, 11, x_52);
lean_ctor_set(x_57, 12, x_53);
lean_ctor_set(x_57, 13, x_54);
lean_ctor_set(x_57, 14, x_55);
lean_ctor_set(x_57, 15, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*16, x_48);
x_58 = lean_st_ref_set(x_27, x_57, x_32);
lean_dec(x_27);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_4);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_63 = lean_ctor_get(x_29, 0);
x_64 = lean_ctor_get(x_29, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_29);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_inc(x_4);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_24);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_26);
x_70 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(x_67, x_22, x_69);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc_n(x_4, 2);
x_72 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_71, x_4, x_4);
x_73 = lean_ctor_get(x_66, 2);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_ctor_get(x_63, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_63, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_63, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_63, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_63, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_63, 7);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_63, sizeof(void*)*16);
x_82 = lean_ctor_get(x_63, 8);
lean_inc(x_82);
x_83 = lean_ctor_get(x_63, 9);
lean_inc(x_83);
x_84 = lean_ctor_get(x_63, 10);
lean_inc(x_84);
x_85 = lean_ctor_get(x_63, 11);
lean_inc(x_85);
x_86 = lean_ctor_get(x_63, 12);
lean_inc(x_86);
x_87 = lean_ctor_get(x_63, 13);
lean_inc(x_87);
x_88 = lean_ctor_get(x_63, 14);
lean_inc(x_88);
x_89 = lean_ctor_get(x_63, 15);
lean_inc(x_89);
lean_dec(x_63);
x_90 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_90, 0, x_65);
lean_ctor_set(x_90, 1, x_74);
lean_ctor_set(x_90, 2, x_75);
lean_ctor_set(x_90, 3, x_76);
lean_ctor_set(x_90, 4, x_77);
lean_ctor_set(x_90, 5, x_78);
lean_ctor_set(x_90, 6, x_79);
lean_ctor_set(x_90, 7, x_80);
lean_ctor_set(x_90, 8, x_82);
lean_ctor_set(x_90, 9, x_83);
lean_ctor_set(x_90, 10, x_84);
lean_ctor_set(x_90, 11, x_85);
lean_ctor_set(x_90, 12, x_86);
lean_ctor_set(x_90, 13, x_87);
lean_ctor_set(x_90, 14, x_88);
lean_ctor_set(x_90, 15, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*16, x_81);
x_91 = lean_st_ref_set(x_27, x_90, x_64);
lean_dec(x_27);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_4);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
block_178:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_21);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_96);
lean_inc(x_4);
lean_inc(x_98);
lean_inc(x_24);
x_99 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(x_24, x_98, x_4, x_5, x_1, x_96, x_96, x_98, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_mk_string_unchecked("grind", 5, 5);
x_104 = lean_mk_string_unchecked("debug", 5, 5);
x_105 = lean_mk_string_unchecked("canon", 5, 5);
x_106 = l_Lean_Name_mkStr3(x_103, x_104, x_105);
lean_inc(x_106);
x_107 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_106, x_12, x_102);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_106);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_26 = x_96;
x_27 = x_6;
x_28 = x_110;
goto block_95;
}
else
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_107, 1);
x_113 = lean_ctor_get(x_107, 0);
lean_dec(x_113);
x_114 = l_Lean_Meta_Grind_updateLastTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_112);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_mk_string_unchecked("(", 1, 1);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_107, 7);
lean_ctor_set(x_107, 1, x_118);
lean_ctor_set(x_107, 0, x_117);
x_119 = lean_mk_string_unchecked(", ", 2, 2);
x_120 = l_Lean_stringToMessageData(x_119);
lean_dec(x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_120);
x_122 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_Lean_MessageData_ofFormat(x_123);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked(") ↦ ", 6, 4);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
lean_inc(x_4);
x_129 = l_Lean_MessageData_ofExpr(x_4);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_mk_string_unchecked("", 0, 0);
x_132 = l_Lean_stringToMessageData(x_131);
lean_dec(x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_106, x_133, x_10, x_11, x_12, x_13, x_115);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_26 = x_96;
x_27 = x_6;
x_28 = x_135;
goto block_95;
}
else
{
uint8_t x_136; 
lean_free_object(x_107);
lean_dec(x_106);
lean_dec(x_96);
lean_dec(x_22);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_114);
if (x_136 == 0)
{
return x_114;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_114, 0);
x_138 = lean_ctor_get(x_114, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_114);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_107, 1);
lean_inc(x_140);
lean_dec(x_107);
x_141 = l_Lean_Meta_Grind_updateLastTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_140);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_143 = lean_mk_string_unchecked("(", 1, 1);
x_144 = l_Lean_stringToMessageData(x_143);
lean_dec(x_143);
x_145 = l_Lean_MessageData_ofExpr(x_2);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_mk_string_unchecked(", ", 2, 2);
x_148 = l_Lean_stringToMessageData(x_147);
lean_dec(x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
x_150 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_151 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l_Lean_MessageData_ofFormat(x_151);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_mk_string_unchecked(") ↦ ", 6, 4);
x_155 = l_Lean_stringToMessageData(x_154);
lean_dec(x_154);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
lean_inc(x_4);
x_157 = l_Lean_MessageData_ofExpr(x_4);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_mk_string_unchecked("", 0, 0);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_106, x_161, x_10, x_11, x_12, x_13, x_142);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_26 = x_96;
x_27 = x_6;
x_28 = x_163;
goto block_95;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_106);
lean_dec(x_96);
lean_dec(x_22);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = lean_ctor_get(x_141, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_141, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_166 = x_141;
} else {
 lean_dec_ref(x_141);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_96);
lean_dec(x_22);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_99);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_99, 0);
lean_dec(x_169);
x_170 = lean_ctor_get(x_101, 0);
lean_inc(x_170);
lean_dec(x_101);
lean_ctor_set(x_99, 0, x_170);
return x_99;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_99, 1);
lean_inc(x_171);
lean_dec(x_99);
x_172 = lean_ctor_get(x_101, 0);
lean_inc(x_172);
lean_dec(x_101);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_96);
lean_dec(x_22);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = !lean_is_exclusive(x_99);
if (x_174 == 0)
{
return x_99;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_99, 0);
x_176 = lean_ctor_get(x_99, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_99);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_224; lean_object* x_277; lean_object* x_278; 
x_183 = lean_ctor_get(x_22, 0);
x_184 = lean_ctor_get(x_22, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_22);
lean_inc(x_3);
lean_inc(x_2);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_2);
lean_ctor_set(x_185, 1, x_3);
x_277 = lean_ctor_get(x_19, 0);
lean_inc(x_277);
lean_dec(x_19);
x_278 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg(x_277, x_185);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; 
x_279 = lean_box(0);
x_224 = x_279;
goto block_276;
}
else
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
lean_dec(x_278);
x_224 = x_280;
goto block_276;
}
block_223:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_189 = lean_st_ref_take(x_187, x_188);
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
x_193 = lean_ctor_get(x_190, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_inc(x_4);
if (lean_is_scalar(x_192)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_192;
}
lean_ctor_set(x_196, 0, x_4);
lean_ctor_set(x_196, 1, x_183);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_186);
x_198 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(x_195, x_185, x_197);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_inc_n(x_4, 2);
x_200 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_199, x_4, x_4);
x_201 = lean_ctor_get(x_194, 2);
lean_inc(x_201);
lean_dec(x_194);
x_202 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_202, 0, x_198);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_201);
x_203 = lean_ctor_get(x_190, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_190, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_190, 4);
lean_inc(x_205);
x_206 = lean_ctor_get(x_190, 5);
lean_inc(x_206);
x_207 = lean_ctor_get(x_190, 6);
lean_inc(x_207);
x_208 = lean_ctor_get(x_190, 7);
lean_inc(x_208);
x_209 = lean_ctor_get_uint8(x_190, sizeof(void*)*16);
x_210 = lean_ctor_get(x_190, 8);
lean_inc(x_210);
x_211 = lean_ctor_get(x_190, 9);
lean_inc(x_211);
x_212 = lean_ctor_get(x_190, 10);
lean_inc(x_212);
x_213 = lean_ctor_get(x_190, 11);
lean_inc(x_213);
x_214 = lean_ctor_get(x_190, 12);
lean_inc(x_214);
x_215 = lean_ctor_get(x_190, 13);
lean_inc(x_215);
x_216 = lean_ctor_get(x_190, 14);
lean_inc(x_216);
x_217 = lean_ctor_get(x_190, 15);
lean_inc(x_217);
lean_dec(x_190);
x_218 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_218, 0, x_193);
lean_ctor_set(x_218, 1, x_202);
lean_ctor_set(x_218, 2, x_203);
lean_ctor_set(x_218, 3, x_204);
lean_ctor_set(x_218, 4, x_205);
lean_ctor_set(x_218, 5, x_206);
lean_ctor_set(x_218, 6, x_207);
lean_ctor_set(x_218, 7, x_208);
lean_ctor_set(x_218, 8, x_210);
lean_ctor_set(x_218, 9, x_211);
lean_ctor_set(x_218, 10, x_212);
lean_ctor_set(x_218, 11, x_213);
lean_ctor_set(x_218, 12, x_214);
lean_ctor_set(x_218, 13, x_215);
lean_ctor_set(x_218, 14, x_216);
lean_ctor_set(x_218, 15, x_217);
lean_ctor_set_uint8(x_218, sizeof(void*)*16, x_209);
x_219 = lean_st_ref_set(x_187, x_218, x_191);
lean_dec(x_187);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_4);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
block_276:
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_box(0);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_21);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_224);
lean_inc(x_4);
lean_inc(x_226);
lean_inc(x_183);
x_227 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(x_183, x_226, x_4, x_5, x_1, x_224, x_224, x_226, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_184);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec(x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_mk_string_unchecked("grind", 5, 5);
x_232 = lean_mk_string_unchecked("debug", 5, 5);
x_233 = lean_mk_string_unchecked("canon", 5, 5);
x_234 = l_Lean_Name_mkStr3(x_231, x_232, x_233);
lean_inc(x_234);
x_235 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_234, x_12, x_230);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_unbox(x_236);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; 
lean_dec(x_234);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_186 = x_224;
x_187 = x_6;
x_188 = x_238;
goto block_223;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_240 = x_235;
} else {
 lean_dec_ref(x_235);
 x_240 = lean_box(0);
}
x_241 = l_Lean_Meta_Grind_updateLastTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_239);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_mk_string_unchecked("(", 1, 1);
x_244 = l_Lean_stringToMessageData(x_243);
lean_dec(x_243);
x_245 = l_Lean_MessageData_ofExpr(x_2);
if (lean_is_scalar(x_240)) {
 x_246 = lean_alloc_ctor(7, 2, 0);
} else {
 x_246 = x_240;
 lean_ctor_set_tag(x_246, 7);
}
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_mk_string_unchecked(", ", 2, 2);
x_248 = l_Lean_stringToMessageData(x_247);
lean_dec(x_247);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
x_250 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_251 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_252 = l_Lean_MessageData_ofFormat(x_251);
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_mk_string_unchecked(") ↦ ", 6, 4);
x_255 = l_Lean_stringToMessageData(x_254);
lean_dec(x_254);
x_256 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_255);
lean_inc(x_4);
x_257 = l_Lean_MessageData_ofExpr(x_4);
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_mk_string_unchecked("", 0, 0);
x_260 = l_Lean_stringToMessageData(x_259);
lean_dec(x_259);
x_261 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_234, x_261, x_10, x_11, x_12, x_13, x_242);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_186 = x_224;
x_187 = x_6;
x_188 = x_263;
goto block_223;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_240);
lean_dec(x_234);
lean_dec(x_224);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_264 = lean_ctor_get(x_241, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_241, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_266 = x_241;
} else {
 lean_dec_ref(x_241);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_224);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_268 = lean_ctor_get(x_227, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_269 = x_227;
} else {
 lean_dec_ref(x_227);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_229, 0);
lean_inc(x_270);
lean_dec(x_229);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_268);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_224);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_272 = lean_ctor_get(x_227, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_227, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_274 = x_227;
} else {
 lean_dec_ref(x_227);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
else
{
lean_object* x_281; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = lean_ctor_get(x_21, 0);
lean_inc(x_281);
lean_dec(x_21);
lean_ctor_set(x_15, 0, x_281);
return x_15;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_15, 0);
x_283 = lean_ctor_get(x_15, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_15);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
x_286 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_mkAuxLemma_spec__0___redArg(x_285, x_4);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_287 = lean_infer_type(x_4, x_10, x_11, x_12, x_13, x_283);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_330; lean_object* x_383; lean_object* x_384; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_2);
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_2);
lean_ctor_set(x_291, 1, x_3);
x_383 = lean_ctor_get(x_284, 0);
lean_inc(x_383);
lean_dec(x_284);
x_384 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg(x_383, x_291);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; 
x_385 = lean_box(0);
x_330 = x_385;
goto block_382;
}
else
{
lean_object* x_386; 
x_386 = lean_ctor_get(x_384, 0);
lean_inc(x_386);
lean_dec(x_384);
x_330 = x_386;
goto block_382;
}
block_329:
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_295 = lean_st_ref_take(x_293, x_294);
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
x_299 = lean_ctor_get(x_296, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
lean_inc(x_4);
if (lean_is_scalar(x_298)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_298;
}
lean_ctor_set(x_302, 0, x_4);
lean_ctor_set(x_302, 1, x_288);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_292);
x_304 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(x_301, x_291, x_303);
x_305 = lean_ctor_get(x_300, 1);
lean_inc(x_305);
lean_inc_n(x_4, 2);
x_306 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_305, x_4, x_4);
x_307 = lean_ctor_get(x_300, 2);
lean_inc(x_307);
lean_dec(x_300);
x_308 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_306);
lean_ctor_set(x_308, 2, x_307);
x_309 = lean_ctor_get(x_296, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_296, 3);
lean_inc(x_310);
x_311 = lean_ctor_get(x_296, 4);
lean_inc(x_311);
x_312 = lean_ctor_get(x_296, 5);
lean_inc(x_312);
x_313 = lean_ctor_get(x_296, 6);
lean_inc(x_313);
x_314 = lean_ctor_get(x_296, 7);
lean_inc(x_314);
x_315 = lean_ctor_get_uint8(x_296, sizeof(void*)*16);
x_316 = lean_ctor_get(x_296, 8);
lean_inc(x_316);
x_317 = lean_ctor_get(x_296, 9);
lean_inc(x_317);
x_318 = lean_ctor_get(x_296, 10);
lean_inc(x_318);
x_319 = lean_ctor_get(x_296, 11);
lean_inc(x_319);
x_320 = lean_ctor_get(x_296, 12);
lean_inc(x_320);
x_321 = lean_ctor_get(x_296, 13);
lean_inc(x_321);
x_322 = lean_ctor_get(x_296, 14);
lean_inc(x_322);
x_323 = lean_ctor_get(x_296, 15);
lean_inc(x_323);
lean_dec(x_296);
x_324 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_324, 0, x_299);
lean_ctor_set(x_324, 1, x_308);
lean_ctor_set(x_324, 2, x_309);
lean_ctor_set(x_324, 3, x_310);
lean_ctor_set(x_324, 4, x_311);
lean_ctor_set(x_324, 5, x_312);
lean_ctor_set(x_324, 6, x_313);
lean_ctor_set(x_324, 7, x_314);
lean_ctor_set(x_324, 8, x_316);
lean_ctor_set(x_324, 9, x_317);
lean_ctor_set(x_324, 10, x_318);
lean_ctor_set(x_324, 11, x_319);
lean_ctor_set(x_324, 12, x_320);
lean_ctor_set(x_324, 13, x_321);
lean_ctor_set(x_324, 14, x_322);
lean_ctor_set(x_324, 15, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*16, x_315);
x_325 = lean_st_ref_set(x_293, x_324, x_297);
lean_dec(x_293);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_4);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
block_382:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_box(0);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_286);
lean_ctor_set(x_332, 1, x_331);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_330);
lean_inc(x_4);
lean_inc(x_332);
lean_inc(x_288);
x_333 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(x_288, x_332, x_4, x_5, x_1, x_330, x_330, x_332, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_289);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
lean_dec(x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
lean_dec(x_333);
x_337 = lean_mk_string_unchecked("grind", 5, 5);
x_338 = lean_mk_string_unchecked("debug", 5, 5);
x_339 = lean_mk_string_unchecked("canon", 5, 5);
x_340 = l_Lean_Name_mkStr3(x_337, x_338, x_339);
lean_inc(x_340);
x_341 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_340, x_12, x_336);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_unbox(x_342);
lean_dec(x_342);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_340);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
lean_dec(x_341);
x_292 = x_330;
x_293 = x_6;
x_294 = x_344;
goto block_329;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_341, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_346 = x_341;
} else {
 lean_dec_ref(x_341);
 x_346 = lean_box(0);
}
x_347 = l_Lean_Meta_Grind_updateLastTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_345);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
lean_dec(x_347);
x_349 = lean_mk_string_unchecked("(", 1, 1);
x_350 = l_Lean_stringToMessageData(x_349);
lean_dec(x_349);
x_351 = l_Lean_MessageData_ofExpr(x_2);
if (lean_is_scalar(x_346)) {
 x_352 = lean_alloc_ctor(7, 2, 0);
} else {
 x_352 = x_346;
 lean_ctor_set_tag(x_352, 7);
}
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_mk_string_unchecked(", ", 2, 2);
x_354 = l_Lean_stringToMessageData(x_353);
lean_dec(x_353);
x_355 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_354);
x_356 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_357 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_357, 0, x_356);
x_358 = l_Lean_MessageData_ofFormat(x_357);
x_359 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_359, 0, x_355);
lean_ctor_set(x_359, 1, x_358);
x_360 = lean_mk_string_unchecked(") ↦ ", 6, 4);
x_361 = l_Lean_stringToMessageData(x_360);
lean_dec(x_360);
x_362 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_361);
lean_inc(x_4);
x_363 = l_Lean_MessageData_ofExpr(x_4);
x_364 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_mk_string_unchecked("", 0, 0);
x_366 = l_Lean_stringToMessageData(x_365);
lean_dec(x_365);
x_367 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_366);
x_368 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_340, x_367, x_10, x_11, x_12, x_13, x_348);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
x_292 = x_330;
x_293 = x_6;
x_294 = x_369;
goto block_329;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_346);
lean_dec(x_340);
lean_dec(x_330);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_370 = lean_ctor_get(x_347, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_347, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_372 = x_347;
} else {
 lean_dec_ref(x_347);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_330);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_374 = lean_ctor_get(x_333, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_375 = x_333;
} else {
 lean_dec_ref(x_333);
 x_375 = lean_box(0);
}
x_376 = lean_ctor_get(x_335, 0);
lean_inc(x_376);
lean_dec(x_335);
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_374);
return x_377;
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_330);
lean_dec(x_291);
lean_dec(x_288);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_378 = lean_ctor_get(x_333, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_333, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_380 = x_333;
} else {
 lean_dec_ref(x_333);
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
}
else
{
lean_dec(x_284);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_287;
}
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_284);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_387 = lean_ctor_get(x_286, 0);
lean_inc(x_387);
lean_dec(x_286);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_283);
return x_388;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___redArg(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1___boxed(lean_object** _args) {
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
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__1(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg___boxed(lean_object** _args) {
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
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1___boxed(lean_object** _args) {
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
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonElemCore_spec__1(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3_spec__3(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_Canon_canonElemCore_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint8_t x_41; uint64_t x_42; uint64_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get_uint8(x_16, 0);
x_18 = lean_ctor_get_uint8(x_16, 1);
x_19 = lean_ctor_get_uint8(x_16, 2);
x_20 = lean_ctor_get_uint8(x_16, 3);
x_21 = lean_ctor_get_uint8(x_16, 4);
x_22 = lean_ctor_get_uint8(x_16, 5);
x_23 = lean_ctor_get_uint8(x_16, 6);
x_24 = lean_ctor_get_uint8(x_16, 7);
x_25 = lean_ctor_get_uint8(x_16, 8);
x_26 = lean_ctor_get_uint8(x_16, 10);
x_27 = lean_ctor_get_uint8(x_16, 11);
x_28 = lean_ctor_get_uint8(x_16, 12);
x_29 = lean_ctor_get_uint8(x_16, 13);
x_30 = lean_ctor_get_uint8(x_16, 14);
x_31 = lean_ctor_get_uint8(x_16, 15);
x_32 = lean_ctor_get_uint8(x_16, 16);
x_33 = lean_ctor_get_uint8(x_16, 17);
x_34 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_34, 0, x_17);
lean_ctor_set_uint8(x_34, 1, x_18);
lean_ctor_set_uint8(x_34, 2, x_19);
lean_ctor_set_uint8(x_34, 3, x_20);
lean_ctor_set_uint8(x_34, 4, x_21);
lean_ctor_set_uint8(x_34, 5, x_22);
lean_ctor_set_uint8(x_34, 6, x_23);
lean_ctor_set_uint8(x_34, 7, x_24);
lean_ctor_set_uint8(x_34, 8, x_25);
x_35 = lean_unbox(x_15);
lean_ctor_set_uint8(x_34, 9, x_35);
lean_ctor_set_uint8(x_34, 10, x_26);
lean_ctor_set_uint8(x_34, 11, x_27);
lean_ctor_set_uint8(x_34, 12, x_28);
lean_ctor_set_uint8(x_34, 13, x_29);
lean_ctor_set_uint8(x_34, 14, x_30);
lean_ctor_set_uint8(x_34, 15, x_31);
lean_ctor_set_uint8(x_34, 16, x_32);
lean_ctor_set_uint8(x_34, 17, x_33);
x_36 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_right(x_36, x_38);
x_40 = lean_uint64_shift_left(x_39, x_38);
x_41 = lean_unbox(x_15);
x_42 = l_Lean_Meta_TransparencyMode_toUInt64(x_41);
x_43 = lean_uint64_lor(x_40, x_42);
x_44 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_45 = lean_ctor_get(x_9, 1);
x_46 = lean_ctor_get(x_9, 2);
x_47 = lean_ctor_get(x_9, 3);
x_48 = lean_ctor_get(x_9, 4);
x_49 = lean_ctor_get(x_9, 5);
x_50 = lean_ctor_get(x_9, 6);
x_51 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_52 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
x_53 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_48);
lean_ctor_set(x_53, 5, x_49);
lean_ctor_set(x_53, 6, x_50);
lean_ctor_set_uint64(x_53, sizeof(void*)*7, x_43);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 8, x_44);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 9, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 10, x_52);
x_54 = lean_unbox(x_14);
x_55 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_54, x_5, x_6, x_7, x_8, x_53, x_10, x_11, x_12, x_13);
return x_55;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Canon_canonType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint8_t x_41; uint64_t x_42; uint64_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_14 = lean_box(1);
x_15 = lean_box(3);
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get_uint8(x_16, 0);
x_18 = lean_ctor_get_uint8(x_16, 1);
x_19 = lean_ctor_get_uint8(x_16, 2);
x_20 = lean_ctor_get_uint8(x_16, 3);
x_21 = lean_ctor_get_uint8(x_16, 4);
x_22 = lean_ctor_get_uint8(x_16, 5);
x_23 = lean_ctor_get_uint8(x_16, 6);
x_24 = lean_ctor_get_uint8(x_16, 7);
x_25 = lean_ctor_get_uint8(x_16, 8);
x_26 = lean_ctor_get_uint8(x_16, 10);
x_27 = lean_ctor_get_uint8(x_16, 11);
x_28 = lean_ctor_get_uint8(x_16, 12);
x_29 = lean_ctor_get_uint8(x_16, 13);
x_30 = lean_ctor_get_uint8(x_16, 14);
x_31 = lean_ctor_get_uint8(x_16, 15);
x_32 = lean_ctor_get_uint8(x_16, 16);
x_33 = lean_ctor_get_uint8(x_16, 17);
x_34 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_34, 0, x_17);
lean_ctor_set_uint8(x_34, 1, x_18);
lean_ctor_set_uint8(x_34, 2, x_19);
lean_ctor_set_uint8(x_34, 3, x_20);
lean_ctor_set_uint8(x_34, 4, x_21);
lean_ctor_set_uint8(x_34, 5, x_22);
lean_ctor_set_uint8(x_34, 6, x_23);
lean_ctor_set_uint8(x_34, 7, x_24);
lean_ctor_set_uint8(x_34, 8, x_25);
x_35 = lean_unbox(x_15);
lean_ctor_set_uint8(x_34, 9, x_35);
lean_ctor_set_uint8(x_34, 10, x_26);
lean_ctor_set_uint8(x_34, 11, x_27);
lean_ctor_set_uint8(x_34, 12, x_28);
lean_ctor_set_uint8(x_34, 13, x_29);
lean_ctor_set_uint8(x_34, 14, x_30);
lean_ctor_set_uint8(x_34, 15, x_31);
lean_ctor_set_uint8(x_34, 16, x_32);
lean_ctor_set_uint8(x_34, 17, x_33);
x_36 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_right(x_36, x_38);
x_40 = lean_uint64_shift_left(x_39, x_38);
x_41 = lean_unbox(x_15);
x_42 = l_Lean_Meta_TransparencyMode_toUInt64(x_41);
x_43 = lean_uint64_lor(x_40, x_42);
x_44 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_45 = lean_ctor_get(x_9, 1);
x_46 = lean_ctor_get(x_9, 2);
x_47 = lean_ctor_get(x_9, 3);
x_48 = lean_ctor_get(x_9, 4);
x_49 = lean_ctor_get(x_9, 5);
x_50 = lean_ctor_get(x_9, 6);
x_51 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_52 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
x_53 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_48);
lean_ctor_set(x_53, 5, x_49);
lean_ctor_set(x_53, 6, x_50);
lean_ctor_set_uint64(x_53, sizeof(void*)*7, x_43);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 8, x_44);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 9, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 10, x_52);
x_54 = lean_unbox(x_14);
x_55 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_54, x_5, x_6, x_7, x_8, x_53, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Canon_canonInst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint8_t x_41; uint64_t x_42; uint64_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_14 = lean_box(1);
x_15 = lean_box(2);
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get_uint8(x_16, 0);
x_18 = lean_ctor_get_uint8(x_16, 1);
x_19 = lean_ctor_get_uint8(x_16, 2);
x_20 = lean_ctor_get_uint8(x_16, 3);
x_21 = lean_ctor_get_uint8(x_16, 4);
x_22 = lean_ctor_get_uint8(x_16, 5);
x_23 = lean_ctor_get_uint8(x_16, 6);
x_24 = lean_ctor_get_uint8(x_16, 7);
x_25 = lean_ctor_get_uint8(x_16, 8);
x_26 = lean_ctor_get_uint8(x_16, 10);
x_27 = lean_ctor_get_uint8(x_16, 11);
x_28 = lean_ctor_get_uint8(x_16, 12);
x_29 = lean_ctor_get_uint8(x_16, 13);
x_30 = lean_ctor_get_uint8(x_16, 14);
x_31 = lean_ctor_get_uint8(x_16, 15);
x_32 = lean_ctor_get_uint8(x_16, 16);
x_33 = lean_ctor_get_uint8(x_16, 17);
x_34 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_34, 0, x_17);
lean_ctor_set_uint8(x_34, 1, x_18);
lean_ctor_set_uint8(x_34, 2, x_19);
lean_ctor_set_uint8(x_34, 3, x_20);
lean_ctor_set_uint8(x_34, 4, x_21);
lean_ctor_set_uint8(x_34, 5, x_22);
lean_ctor_set_uint8(x_34, 6, x_23);
lean_ctor_set_uint8(x_34, 7, x_24);
lean_ctor_set_uint8(x_34, 8, x_25);
x_35 = lean_unbox(x_15);
lean_ctor_set_uint8(x_34, 9, x_35);
lean_ctor_set_uint8(x_34, 10, x_26);
lean_ctor_set_uint8(x_34, 11, x_27);
lean_ctor_set_uint8(x_34, 12, x_28);
lean_ctor_set_uint8(x_34, 13, x_29);
lean_ctor_set_uint8(x_34, 14, x_30);
lean_ctor_set_uint8(x_34, 15, x_31);
lean_ctor_set_uint8(x_34, 16, x_32);
lean_ctor_set_uint8(x_34, 17, x_33);
x_36 = lean_ctor_get_uint64(x_9, sizeof(void*)*7);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_right(x_36, x_38);
x_40 = lean_uint64_shift_left(x_39, x_38);
x_41 = lean_unbox(x_15);
x_42 = l_Lean_Meta_TransparencyMode_toUInt64(x_41);
x_43 = lean_uint64_lor(x_40, x_42);
x_44 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_45 = lean_ctor_get(x_9, 1);
x_46 = lean_ctor_get(x_9, 2);
x_47 = lean_ctor_get(x_9, 3);
x_48 = lean_ctor_get(x_9, 4);
x_49 = lean_ctor_get(x_9, 5);
x_50 = lean_ctor_get(x_9, 6);
x_51 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_52 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
x_53 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_48);
lean_ctor_set(x_53, 5, x_49);
lean_ctor_set(x_53, 6, x_50);
lean_ctor_set_uint64(x_53, sizeof(void*)*7, x_43);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 8, x_44);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 9, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*7 + 10, x_52);
x_54 = lean_unbox(x_14);
x_55 = l_Lean_Meta_Grind_Canon_canonElemCore(x_1, x_2, x_3, x_4, x_54, x_5, x_6, x_7, x_8, x_53, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImplicit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Canon_canonImplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("canonType", 9, 9);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("canonInst", 9, 9);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_mk_string_unchecked("canonImplicit", 13, 13);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_mk_string_unchecked("visit", 5, 5);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_48; uint8_t x_49; 
x_48 = lean_array_get_size(x_1);
x_49 = lean_nat_dec_lt(x_2, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
goto block_47;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_array_fget(x_1, x_2);
x_51 = l_Lean_Meta_ParamInfo_isInstImplicit(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = lean_ctor_get_uint8(x_50, sizeof(void*)*1 + 2);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Meta_ParamInfo_isImplicit(x_50);
lean_dec(x_50);
if (x_53 == 0)
{
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
goto block_47;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_Meta_isTypeFormer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 0);
lean_dec(x_58);
x_59 = lean_box(2);
lean_ctor_set(x_54, 0, x_59);
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_box(2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_54, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set(x_54, 0, x_65);
return x_54;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_54);
if (x_69 == 0)
{
return x_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_54, 0);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = lean_box(3);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_8);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_box(1);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_8);
return x_76;
}
}
block_47:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_14 = l_Lean_Meta_isProp(x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_isTypeFormer(x_3, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_box(3);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_box(3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_14, 0);
lean_dec(x_38);
x_39 = lean_box(3);
lean_ctor_set(x_14, 0, x_39);
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_dec(x_14);
x_41 = lean_box(3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Canon_shouldCanon(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ptr_addr(x_5);
x_9 = lean_ptr_addr(x_1);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_11);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_ptr_addr(x_12);
x_16 = lean_ptr_addr(x_1);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(x_1, x_2, x_14);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(x_1, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; double x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_float_of_nat(x_22);
x_24 = lean_box(0);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_27);
x_28 = lean_mk_empty_array_with_capacity(x_22);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_15);
lean_ctor_set(x_11, 1, x_29);
lean_ctor_set(x_11, 0, x_15);
x_30 = l_Lean_PersistentArray_push___redArg(x_21, x_11);
x_31 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_20);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 7);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_17);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_35);
x_37 = lean_st_ref_set(x_6, x_36, x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; double x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_ctor_get(x_5, 5);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_50, sizeof(void*)*1);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_float_of_nat(x_53);
x_55 = lean_box(0);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_float(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_float(x_57, sizeof(void*)*2 + 8, x_54);
x_58 = lean_unbox(x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 16, x_58);
x_59 = lean_mk_empty_array_with_capacity(x_53);
x_60 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_9);
lean_ctor_set(x_60, 2, x_59);
lean_inc(x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentArray_push___redArg(x_52, x_61);
x_63 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint64(x_63, sizeof(void*)*1, x_51);
x_64 = lean_ctor_get(x_44, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_44, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 7);
lean_inc(x_67);
lean_dec(x_44);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_6, x_68, x_45);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_6, 1);
x_26 = lean_nat_dec_lt(x_8, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_236; 
x_28 = lean_mk_string_unchecked("grind", 5, 5);
x_29 = lean_mk_string_unchecked("debug", 5, 5);
x_30 = lean_mk_string_unchecked("canon", 5, 5);
x_31 = l_Lean_Name_mkStr3(x_28, x_29, x_30);
lean_inc(x_31);
x_32 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(x_31, x_16, x_18);
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
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_dec(x_7);
x_38 = lean_array_fget(x_36, x_8);
x_236 = lean_unbox(x_33);
lean_dec(x_33);
if (x_236 == 0)
{
lean_dec(x_31);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_52 = x_9;
x_53 = x_10;
x_54 = x_11;
x_55 = x_12;
x_56 = x_13;
x_57 = x_14;
x_58 = x_15;
x_59 = x_16;
x_60 = x_17;
x_61 = x_34;
goto block_235;
}
else
{
lean_object* x_237; 
x_237 = l_Lean_Meta_Grind_updateLastTag(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_34);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_38);
x_239 = l_Lean_Meta_Grind_Canon_shouldCanon(x_2, x_8, x_38, x_14, x_15, x_16, x_17, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_38);
x_242 = lean_infer_type(x_38, x_14, x_15, x_16, x_17, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_266; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_mk_string_unchecked("[", 1, 1);
x_246 = l_Lean_stringToMessageData(x_245);
lean_dec(x_245);
x_266 = lean_unbox(x_240);
lean_dec(x_240);
switch (x_266) {
case 0:
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_mk_string_unchecked("canonType", 9, 9);
x_268 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_268, 0, x_267);
x_247 = x_268;
goto block_265;
}
case 1:
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_mk_string_unchecked("canonInst", 9, 9);
x_270 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_270, 0, x_269);
x_247 = x_270;
goto block_265;
}
case 2:
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_mk_string_unchecked("canonImplicit", 13, 13);
x_272 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_272, 0, x_271);
x_247 = x_272;
goto block_265;
}
default: 
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_mk_string_unchecked("visit", 5, 5);
x_274 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_247 = x_274;
goto block_265;
}
}
block_265:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_248 = l_Lean_MessageData_ofFormat(x_247);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_mk_string_unchecked("]: ", 3, 3);
x_251 = l_Lean_stringToMessageData(x_250);
lean_dec(x_250);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_251);
lean_inc(x_38);
x_253 = l_Lean_MessageData_ofExpr(x_38);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_mk_string_unchecked(" : ", 3, 3);
x_256 = l_Lean_stringToMessageData(x_255);
lean_dec(x_255);
x_257 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Lean_MessageData_ofExpr(x_243);
x_259 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_mk_string_unchecked("", 0, 0);
x_261 = l_Lean_stringToMessageData(x_260);
lean_dec(x_260);
x_262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_261);
x_263 = l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(x_31, x_262, x_14, x_15, x_16, x_17, x_244);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_52 = x_9;
x_53 = x_10;
x_54 = x_11;
x_55 = x_12;
x_56 = x_13;
x_57 = x_14;
x_58 = x_15;
x_59 = x_16;
x_60 = x_17;
x_61 = x_264;
goto block_235;
}
}
else
{
uint8_t x_275; 
lean_dec(x_240);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_275 = !lean_is_exclusive(x_242);
if (x_275 == 0)
{
return x_242;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_242, 0);
x_277 = lean_ctor_get(x_242, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_242);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_279 = !lean_is_exclusive(x_239);
if (x_279 == 0)
{
return x_239;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_239, 0);
x_281 = lean_ctor_get(x_239, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_239);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_283 = !lean_is_exclusive(x_237);
if (x_283 == 0)
{
return x_237;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_237, 0);
x_285 = lean_ctor_get(x_237, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_237);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
block_51:
{
size_t x_43; size_t x_44; uint8_t x_45; 
x_43 = lean_ptr_addr(x_38);
lean_dec(x_38);
x_44 = lean_ptr_addr(x_41);
x_45 = lean_usize_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_array_fset(x_39, x_8, x_41);
x_47 = lean_box(x_1);
if (lean_is_scalar(x_35)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_35;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_19 = x_48;
x_20 = x_42;
goto block_24;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
x_49 = lean_box(x_40);
if (lean_is_scalar(x_35)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_35;
}
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_49);
x_19 = x_50;
x_20 = x_42;
goto block_24;
}
}
block_235:
{
lean_object* x_62; 
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_38);
x_62 = l_Lean_Meta_Grind_Canon_shouldCanon(x_2, x_8, x_38, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
switch (x_64) {
case 0:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; uint64_t x_87; lean_object* x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint8_t x_92; uint64_t x_93; uint64_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_52);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_box(1);
x_67 = lean_ctor_get(x_57, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_67, 0);
x_69 = lean_ctor_get_uint8(x_67, 1);
x_70 = lean_ctor_get_uint8(x_67, 2);
x_71 = lean_ctor_get_uint8(x_67, 3);
x_72 = lean_ctor_get_uint8(x_67, 4);
x_73 = lean_ctor_get_uint8(x_67, 5);
x_74 = lean_ctor_get_uint8(x_67, 6);
x_75 = lean_ctor_get_uint8(x_67, 7);
x_76 = lean_ctor_get_uint8(x_67, 8);
x_77 = lean_ctor_get_uint8(x_67, 10);
x_78 = lean_ctor_get_uint8(x_67, 11);
x_79 = lean_ctor_get_uint8(x_67, 12);
x_80 = lean_ctor_get_uint8(x_67, 13);
x_81 = lean_ctor_get_uint8(x_67, 14);
x_82 = lean_ctor_get_uint8(x_67, 15);
x_83 = lean_ctor_get_uint8(x_67, 16);
x_84 = lean_ctor_get_uint8(x_67, 17);
lean_dec(x_67);
x_85 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_85, 0, x_68);
lean_ctor_set_uint8(x_85, 1, x_69);
lean_ctor_set_uint8(x_85, 2, x_70);
lean_ctor_set_uint8(x_85, 3, x_71);
lean_ctor_set_uint8(x_85, 4, x_72);
lean_ctor_set_uint8(x_85, 5, x_73);
lean_ctor_set_uint8(x_85, 6, x_74);
lean_ctor_set_uint8(x_85, 7, x_75);
lean_ctor_set_uint8(x_85, 8, x_76);
x_86 = lean_unbox(x_66);
lean_ctor_set_uint8(x_85, 9, x_86);
lean_ctor_set_uint8(x_85, 10, x_77);
lean_ctor_set_uint8(x_85, 11, x_78);
lean_ctor_set_uint8(x_85, 12, x_79);
lean_ctor_set_uint8(x_85, 13, x_80);
lean_ctor_set_uint8(x_85, 14, x_81);
lean_ctor_set_uint8(x_85, 15, x_82);
lean_ctor_set_uint8(x_85, 16, x_83);
lean_ctor_set_uint8(x_85, 17, x_84);
x_87 = lean_ctor_get_uint64(x_57, sizeof(void*)*7);
x_88 = lean_unsigned_to_nat(2u);
x_89 = lean_uint64_of_nat(x_88);
x_90 = lean_uint64_shift_right(x_87, x_89);
x_91 = lean_uint64_shift_left(x_90, x_89);
x_92 = lean_unbox(x_66);
x_93 = l_Lean_Meta_TransparencyMode_toUInt64(x_92);
x_94 = lean_uint64_lor(x_91, x_93);
x_95 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 8);
x_96 = lean_ctor_get(x_57, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_57, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_57, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_57, 4);
lean_inc(x_99);
x_100 = lean_ctor_get(x_57, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_57, 6);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 9);
x_103 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 10);
lean_dec(x_57);
x_104 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_104, 0, x_85);
lean_ctor_set(x_104, 1, x_96);
lean_ctor_set(x_104, 2, x_97);
lean_ctor_set(x_104, 3, x_98);
lean_ctor_set(x_104, 4, x_99);
lean_ctor_set(x_104, 5, x_100);
lean_ctor_set(x_104, 6, x_101);
lean_ctor_set_uint64(x_104, sizeof(void*)*7, x_94);
lean_ctor_set_uint8(x_104, sizeof(void*)*7 + 8, x_95);
lean_ctor_set_uint8(x_104, sizeof(void*)*7 + 9, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*7 + 10, x_103);
lean_inc(x_38);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_105 = l_Lean_Meta_Grind_Canon_canonElemCore(x_3, x_4, x_8, x_38, x_5, x_53, x_54, x_55, x_56, x_104, x_58, x_59, x_60, x_65);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_unbox(x_37);
lean_dec(x_37);
x_39 = x_36;
x_40 = x_108;
x_41 = x_106;
x_42 = x_107;
goto block_51;
}
else
{
uint8_t x_109; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_105);
if (x_109 == 0)
{
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_105, 0);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_105);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
case 1:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; uint8_t x_134; uint64_t x_135; lean_object* x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint8_t x_140; uint64_t x_141; uint64_t x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_52);
x_113 = lean_ctor_get(x_62, 1);
lean_inc(x_113);
lean_dec(x_62);
x_114 = lean_box(3);
x_115 = lean_ctor_get(x_57, 0);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_115, 0);
x_117 = lean_ctor_get_uint8(x_115, 1);
x_118 = lean_ctor_get_uint8(x_115, 2);
x_119 = lean_ctor_get_uint8(x_115, 3);
x_120 = lean_ctor_get_uint8(x_115, 4);
x_121 = lean_ctor_get_uint8(x_115, 5);
x_122 = lean_ctor_get_uint8(x_115, 6);
x_123 = lean_ctor_get_uint8(x_115, 7);
x_124 = lean_ctor_get_uint8(x_115, 8);
x_125 = lean_ctor_get_uint8(x_115, 10);
x_126 = lean_ctor_get_uint8(x_115, 11);
x_127 = lean_ctor_get_uint8(x_115, 12);
x_128 = lean_ctor_get_uint8(x_115, 13);
x_129 = lean_ctor_get_uint8(x_115, 14);
x_130 = lean_ctor_get_uint8(x_115, 15);
x_131 = lean_ctor_get_uint8(x_115, 16);
x_132 = lean_ctor_get_uint8(x_115, 17);
lean_dec(x_115);
x_133 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_133, 0, x_116);
lean_ctor_set_uint8(x_133, 1, x_117);
lean_ctor_set_uint8(x_133, 2, x_118);
lean_ctor_set_uint8(x_133, 3, x_119);
lean_ctor_set_uint8(x_133, 4, x_120);
lean_ctor_set_uint8(x_133, 5, x_121);
lean_ctor_set_uint8(x_133, 6, x_122);
lean_ctor_set_uint8(x_133, 7, x_123);
lean_ctor_set_uint8(x_133, 8, x_124);
x_134 = lean_unbox(x_114);
lean_ctor_set_uint8(x_133, 9, x_134);
lean_ctor_set_uint8(x_133, 10, x_125);
lean_ctor_set_uint8(x_133, 11, x_126);
lean_ctor_set_uint8(x_133, 12, x_127);
lean_ctor_set_uint8(x_133, 13, x_128);
lean_ctor_set_uint8(x_133, 14, x_129);
lean_ctor_set_uint8(x_133, 15, x_130);
lean_ctor_set_uint8(x_133, 16, x_131);
lean_ctor_set_uint8(x_133, 17, x_132);
x_135 = lean_ctor_get_uint64(x_57, sizeof(void*)*7);
x_136 = lean_unsigned_to_nat(2u);
x_137 = lean_uint64_of_nat(x_136);
x_138 = lean_uint64_shift_right(x_135, x_137);
x_139 = lean_uint64_shift_left(x_138, x_137);
x_140 = lean_unbox(x_114);
x_141 = l_Lean_Meta_TransparencyMode_toUInt64(x_140);
x_142 = lean_uint64_lor(x_139, x_141);
x_143 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 8);
x_144 = lean_ctor_get(x_57, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_57, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_57, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_57, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_57, 5);
lean_inc(x_148);
x_149 = lean_ctor_get(x_57, 6);
lean_inc(x_149);
x_150 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 9);
x_151 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 10);
lean_dec(x_57);
x_152 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_152, 0, x_133);
lean_ctor_set(x_152, 1, x_144);
lean_ctor_set(x_152, 2, x_145);
lean_ctor_set(x_152, 3, x_146);
lean_ctor_set(x_152, 4, x_147);
lean_ctor_set(x_152, 5, x_148);
lean_ctor_set(x_152, 6, x_149);
lean_ctor_set_uint64(x_152, sizeof(void*)*7, x_142);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 8, x_143);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 9, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 10, x_151);
lean_inc(x_38);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_153 = l_Lean_Meta_Grind_Canon_canonElemCore(x_3, x_4, x_8, x_38, x_1, x_53, x_54, x_55, x_56, x_152, x_58, x_59, x_60, x_113);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_unbox(x_37);
lean_dec(x_37);
x_39 = x_36;
x_40 = x_156;
x_41 = x_154;
x_42 = x_155;
goto block_51;
}
else
{
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_dec(x_153);
x_159 = lean_unbox(x_37);
lean_dec(x_37);
x_39 = x_36;
x_40 = x_159;
x_41 = x_157;
x_42 = x_158;
goto block_51;
}
else
{
uint8_t x_160; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_153);
if (x_160 == 0)
{
return x_153;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_153, 0);
x_162 = lean_ctor_get(x_153, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_153);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
case 2:
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_62, 1);
lean_inc(x_164);
lean_dec(x_62);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_38);
x_165 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_38, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; uint64_t x_189; lean_object* x_190; uint64_t x_191; uint64_t x_192; uint64_t x_193; uint8_t x_194; uint64_t x_195; uint64_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_box(2);
x_169 = lean_ctor_get(x_57, 0);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_169, 0);
x_171 = lean_ctor_get_uint8(x_169, 1);
x_172 = lean_ctor_get_uint8(x_169, 2);
x_173 = lean_ctor_get_uint8(x_169, 3);
x_174 = lean_ctor_get_uint8(x_169, 4);
x_175 = lean_ctor_get_uint8(x_169, 5);
x_176 = lean_ctor_get_uint8(x_169, 6);
x_177 = lean_ctor_get_uint8(x_169, 7);
x_178 = lean_ctor_get_uint8(x_169, 8);
x_179 = lean_ctor_get_uint8(x_169, 10);
x_180 = lean_ctor_get_uint8(x_169, 11);
x_181 = lean_ctor_get_uint8(x_169, 12);
x_182 = lean_ctor_get_uint8(x_169, 13);
x_183 = lean_ctor_get_uint8(x_169, 14);
x_184 = lean_ctor_get_uint8(x_169, 15);
x_185 = lean_ctor_get_uint8(x_169, 16);
x_186 = lean_ctor_get_uint8(x_169, 17);
lean_dec(x_169);
x_187 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_187, 0, x_170);
lean_ctor_set_uint8(x_187, 1, x_171);
lean_ctor_set_uint8(x_187, 2, x_172);
lean_ctor_set_uint8(x_187, 3, x_173);
lean_ctor_set_uint8(x_187, 4, x_174);
lean_ctor_set_uint8(x_187, 5, x_175);
lean_ctor_set_uint8(x_187, 6, x_176);
lean_ctor_set_uint8(x_187, 7, x_177);
lean_ctor_set_uint8(x_187, 8, x_178);
x_188 = lean_unbox(x_168);
lean_ctor_set_uint8(x_187, 9, x_188);
lean_ctor_set_uint8(x_187, 10, x_179);
lean_ctor_set_uint8(x_187, 11, x_180);
lean_ctor_set_uint8(x_187, 12, x_181);
lean_ctor_set_uint8(x_187, 13, x_182);
lean_ctor_set_uint8(x_187, 14, x_183);
lean_ctor_set_uint8(x_187, 15, x_184);
lean_ctor_set_uint8(x_187, 16, x_185);
lean_ctor_set_uint8(x_187, 17, x_186);
x_189 = lean_ctor_get_uint64(x_57, sizeof(void*)*7);
x_190 = lean_unsigned_to_nat(2u);
x_191 = lean_uint64_of_nat(x_190);
x_192 = lean_uint64_shift_right(x_189, x_191);
x_193 = lean_uint64_shift_left(x_192, x_191);
x_194 = lean_unbox(x_168);
x_195 = l_Lean_Meta_TransparencyMode_toUInt64(x_194);
x_196 = lean_uint64_lor(x_193, x_195);
x_197 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 8);
x_198 = lean_ctor_get(x_57, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_57, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_57, 3);
lean_inc(x_200);
x_201 = lean_ctor_get(x_57, 4);
lean_inc(x_201);
x_202 = lean_ctor_get(x_57, 5);
lean_inc(x_202);
x_203 = lean_ctor_get(x_57, 6);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 9);
x_205 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 10);
lean_dec(x_57);
x_206 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_206, 0, x_187);
lean_ctor_set(x_206, 1, x_198);
lean_ctor_set(x_206, 2, x_199);
lean_ctor_set(x_206, 3, x_200);
lean_ctor_set(x_206, 4, x_201);
lean_ctor_set(x_206, 5, x_202);
lean_ctor_set(x_206, 6, x_203);
lean_ctor_set_uint64(x_206, sizeof(void*)*7, x_196);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 8, x_197);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 9, x_204);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 10, x_205);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_207 = l_Lean_Meta_Grind_Canon_canonElemCore(x_3, x_4, x_8, x_166, x_1, x_53, x_54, x_55, x_56, x_206, x_58, x_59, x_60, x_167);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_unbox(x_37);
lean_dec(x_37);
x_39 = x_36;
x_40 = x_210;
x_41 = x_208;
x_42 = x_209;
goto block_51;
}
else
{
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_211 = lean_ctor_get(x_207, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
lean_dec(x_207);
x_213 = lean_unbox(x_37);
lean_dec(x_37);
x_39 = x_36;
x_40 = x_213;
x_41 = x_211;
x_42 = x_212;
goto block_51;
}
else
{
uint8_t x_214; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_214 = !lean_is_exclusive(x_207);
if (x_214 == 0)
{
return x_207;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_207, 0);
x_216 = lean_ctor_get(x_207, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_207);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_218 = !lean_is_exclusive(x_165);
if (x_218 == 0)
{
return x_165;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_165, 0);
x_220 = lean_ctor_get(x_165, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_165);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
default: 
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_62, 1);
lean_inc(x_222);
lean_dec(x_62);
lean_inc(x_38);
x_223 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_38, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_unbox(x_37);
lean_dec(x_37);
x_39 = x_36;
x_40 = x_226;
x_41 = x_224;
x_42 = x_225;
goto block_51;
}
else
{
uint8_t x_227; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_227 = !lean_is_exclusive(x_223);
if (x_227 == 0)
{
return x_223;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_223, 0);
x_229 = lean_ctor_get(x_223, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_223);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_231 = !lean_is_exclusive(x_62);
if (x_231 == 0)
{
return x_62;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_62, 0);
x_233 = lean_ctor_get(x_62, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_62);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
block_24:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_nat_add(x_8, x_21);
lean_dec(x_8);
x_7 = x_19;
x_8 = x_22;
x_18 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
x_22 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_nat_dec_lt(x_9, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_19);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_237; 
x_29 = lean_mk_string_unchecked("grind", 5, 5);
x_30 = lean_mk_string_unchecked("debug", 5, 5);
x_31 = lean_mk_string_unchecked("canon", 5, 5);
x_32 = l_Lean_Name_mkStr3(x_29, x_30, x_31);
lean_inc(x_32);
x_33 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(x_32, x_17, x_19);
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
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_dec(x_8);
x_39 = lean_array_fget(x_37, x_9);
x_237 = lean_unbox(x_34);
lean_dec(x_34);
if (x_237 == 0)
{
lean_dec(x_32);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_53 = x_10;
x_54 = x_11;
x_55 = x_12;
x_56 = x_13;
x_57 = x_14;
x_58 = x_15;
x_59 = x_16;
x_60 = x_17;
x_61 = x_18;
x_62 = x_35;
goto block_236;
}
else
{
lean_object* x_238; 
x_238 = l_Lean_Meta_Grind_updateLastTag(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_35);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_39);
x_240 = l_Lean_Meta_Grind_Canon_shouldCanon(x_3, x_9, x_39, x_15, x_16, x_17, x_18, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_39);
x_243 = lean_infer_type(x_39, x_15, x_16, x_17, x_18, x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_267; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_mk_string_unchecked("[", 1, 1);
x_247 = l_Lean_stringToMessageData(x_246);
lean_dec(x_246);
x_267 = lean_unbox(x_241);
lean_dec(x_241);
switch (x_267) {
case 0:
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_mk_string_unchecked("canonType", 9, 9);
x_269 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_248 = x_269;
goto block_266;
}
case 1:
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_mk_string_unchecked("canonInst", 9, 9);
x_271 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_248 = x_271;
goto block_266;
}
case 2:
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_mk_string_unchecked("canonImplicit", 13, 13);
x_273 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_248 = x_273;
goto block_266;
}
default: 
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_mk_string_unchecked("visit", 5, 5);
x_275 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_275, 0, x_274);
x_248 = x_275;
goto block_266;
}
}
block_266:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_249 = l_Lean_MessageData_ofFormat(x_248);
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_mk_string_unchecked("]: ", 3, 3);
x_252 = l_Lean_stringToMessageData(x_251);
lean_dec(x_251);
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_252);
lean_inc(x_39);
x_254 = l_Lean_MessageData_ofExpr(x_39);
x_255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_mk_string_unchecked(" : ", 3, 3);
x_257 = l_Lean_stringToMessageData(x_256);
lean_dec(x_256);
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_MessageData_ofExpr(x_244);
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_mk_string_unchecked("", 0, 0);
x_262 = l_Lean_stringToMessageData(x_261);
lean_dec(x_261);
x_263 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_262);
x_264 = l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(x_32, x_263, x_15, x_16, x_17, x_18, x_245);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_53 = x_10;
x_54 = x_11;
x_55 = x_12;
x_56 = x_13;
x_57 = x_14;
x_58 = x_15;
x_59 = x_16;
x_60 = x_17;
x_61 = x_18;
x_62 = x_265;
goto block_236;
}
}
else
{
uint8_t x_276; 
lean_dec(x_241);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_276 = !lean_is_exclusive(x_243);
if (x_276 == 0)
{
return x_243;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_243, 0);
x_278 = lean_ctor_get(x_243, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_243);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_280 = !lean_is_exclusive(x_240);
if (x_280 == 0)
{
return x_240;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_240, 0);
x_282 = lean_ctor_get(x_240, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_240);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_284 = !lean_is_exclusive(x_238);
if (x_284 == 0)
{
return x_238;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_238, 0);
x_286 = lean_ctor_get(x_238, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_238);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
block_52:
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_39);
lean_dec(x_39);
x_45 = lean_ptr_addr(x_42);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_array_fset(x_40, x_9, x_42);
x_48 = lean_box(x_2);
if (lean_is_scalar(x_36)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_36;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_20 = x_49;
x_21 = x_43;
goto block_25;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
x_50 = lean_box(x_41);
if (lean_is_scalar(x_36)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_36;
}
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
x_20 = x_51;
x_21 = x_43;
goto block_25;
}
}
block_236:
{
lean_object* x_63; 
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_39);
x_63 = l_Lean_Meta_Grind_Canon_shouldCanon(x_3, x_9, x_39, x_58, x_59, x_60, x_61, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
switch (x_65) {
case 0:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; uint8_t x_87; uint64_t x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint8_t x_93; uint64_t x_94; uint64_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_53);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_box(1);
x_68 = lean_ctor_get(x_58, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_68, 0);
x_70 = lean_ctor_get_uint8(x_68, 1);
x_71 = lean_ctor_get_uint8(x_68, 2);
x_72 = lean_ctor_get_uint8(x_68, 3);
x_73 = lean_ctor_get_uint8(x_68, 4);
x_74 = lean_ctor_get_uint8(x_68, 5);
x_75 = lean_ctor_get_uint8(x_68, 6);
x_76 = lean_ctor_get_uint8(x_68, 7);
x_77 = lean_ctor_get_uint8(x_68, 8);
x_78 = lean_ctor_get_uint8(x_68, 10);
x_79 = lean_ctor_get_uint8(x_68, 11);
x_80 = lean_ctor_get_uint8(x_68, 12);
x_81 = lean_ctor_get_uint8(x_68, 13);
x_82 = lean_ctor_get_uint8(x_68, 14);
x_83 = lean_ctor_get_uint8(x_68, 15);
x_84 = lean_ctor_get_uint8(x_68, 16);
x_85 = lean_ctor_get_uint8(x_68, 17);
lean_dec(x_68);
x_86 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_86, 0, x_69);
lean_ctor_set_uint8(x_86, 1, x_70);
lean_ctor_set_uint8(x_86, 2, x_71);
lean_ctor_set_uint8(x_86, 3, x_72);
lean_ctor_set_uint8(x_86, 4, x_73);
lean_ctor_set_uint8(x_86, 5, x_74);
lean_ctor_set_uint8(x_86, 6, x_75);
lean_ctor_set_uint8(x_86, 7, x_76);
lean_ctor_set_uint8(x_86, 8, x_77);
x_87 = lean_unbox(x_67);
lean_ctor_set_uint8(x_86, 9, x_87);
lean_ctor_set_uint8(x_86, 10, x_78);
lean_ctor_set_uint8(x_86, 11, x_79);
lean_ctor_set_uint8(x_86, 12, x_80);
lean_ctor_set_uint8(x_86, 13, x_81);
lean_ctor_set_uint8(x_86, 14, x_82);
lean_ctor_set_uint8(x_86, 15, x_83);
lean_ctor_set_uint8(x_86, 16, x_84);
lean_ctor_set_uint8(x_86, 17, x_85);
x_88 = lean_ctor_get_uint64(x_58, sizeof(void*)*7);
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_uint64_of_nat(x_89);
x_91 = lean_uint64_shift_right(x_88, x_90);
x_92 = lean_uint64_shift_left(x_91, x_90);
x_93 = lean_unbox(x_67);
x_94 = l_Lean_Meta_TransparencyMode_toUInt64(x_93);
x_95 = lean_uint64_lor(x_92, x_94);
x_96 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 8);
x_97 = lean_ctor_get(x_58, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_58, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_58, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_58, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_58, 5);
lean_inc(x_101);
x_102 = lean_ctor_get(x_58, 6);
lean_inc(x_102);
x_103 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 9);
x_104 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 10);
lean_dec(x_58);
x_105 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_105, 0, x_86);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_98);
lean_ctor_set(x_105, 3, x_99);
lean_ctor_set(x_105, 4, x_100);
lean_ctor_set(x_105, 5, x_101);
lean_ctor_set(x_105, 6, x_102);
lean_ctor_set_uint64(x_105, sizeof(void*)*7, x_95);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 8, x_96);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 9, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*7 + 10, x_104);
lean_inc(x_39);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_106 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_9, x_39, x_6, x_54, x_55, x_56, x_57, x_105, x_59, x_60, x_61, x_66);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unbox(x_38);
lean_dec(x_38);
x_40 = x_37;
x_41 = x_109;
x_42 = x_107;
x_43 = x_108;
goto block_52;
}
else
{
uint8_t x_110; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 0);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_106);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
case 1:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; uint64_t x_136; lean_object* x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint8_t x_141; uint64_t x_142; uint64_t x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_53);
x_114 = lean_ctor_get(x_63, 1);
lean_inc(x_114);
lean_dec(x_63);
x_115 = lean_box(3);
x_116 = lean_ctor_get(x_58, 0);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_116, 0);
x_118 = lean_ctor_get_uint8(x_116, 1);
x_119 = lean_ctor_get_uint8(x_116, 2);
x_120 = lean_ctor_get_uint8(x_116, 3);
x_121 = lean_ctor_get_uint8(x_116, 4);
x_122 = lean_ctor_get_uint8(x_116, 5);
x_123 = lean_ctor_get_uint8(x_116, 6);
x_124 = lean_ctor_get_uint8(x_116, 7);
x_125 = lean_ctor_get_uint8(x_116, 8);
x_126 = lean_ctor_get_uint8(x_116, 10);
x_127 = lean_ctor_get_uint8(x_116, 11);
x_128 = lean_ctor_get_uint8(x_116, 12);
x_129 = lean_ctor_get_uint8(x_116, 13);
x_130 = lean_ctor_get_uint8(x_116, 14);
x_131 = lean_ctor_get_uint8(x_116, 15);
x_132 = lean_ctor_get_uint8(x_116, 16);
x_133 = lean_ctor_get_uint8(x_116, 17);
lean_dec(x_116);
x_134 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_134, 0, x_117);
lean_ctor_set_uint8(x_134, 1, x_118);
lean_ctor_set_uint8(x_134, 2, x_119);
lean_ctor_set_uint8(x_134, 3, x_120);
lean_ctor_set_uint8(x_134, 4, x_121);
lean_ctor_set_uint8(x_134, 5, x_122);
lean_ctor_set_uint8(x_134, 6, x_123);
lean_ctor_set_uint8(x_134, 7, x_124);
lean_ctor_set_uint8(x_134, 8, x_125);
x_135 = lean_unbox(x_115);
lean_ctor_set_uint8(x_134, 9, x_135);
lean_ctor_set_uint8(x_134, 10, x_126);
lean_ctor_set_uint8(x_134, 11, x_127);
lean_ctor_set_uint8(x_134, 12, x_128);
lean_ctor_set_uint8(x_134, 13, x_129);
lean_ctor_set_uint8(x_134, 14, x_130);
lean_ctor_set_uint8(x_134, 15, x_131);
lean_ctor_set_uint8(x_134, 16, x_132);
lean_ctor_set_uint8(x_134, 17, x_133);
x_136 = lean_ctor_get_uint64(x_58, sizeof(void*)*7);
x_137 = lean_unsigned_to_nat(2u);
x_138 = lean_uint64_of_nat(x_137);
x_139 = lean_uint64_shift_right(x_136, x_138);
x_140 = lean_uint64_shift_left(x_139, x_138);
x_141 = lean_unbox(x_115);
x_142 = l_Lean_Meta_TransparencyMode_toUInt64(x_141);
x_143 = lean_uint64_lor(x_140, x_142);
x_144 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 8);
x_145 = lean_ctor_get(x_58, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_58, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_58, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_58, 4);
lean_inc(x_148);
x_149 = lean_ctor_get(x_58, 5);
lean_inc(x_149);
x_150 = lean_ctor_get(x_58, 6);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 9);
x_152 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 10);
lean_dec(x_58);
x_153 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_153, 0, x_134);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_146);
lean_ctor_set(x_153, 3, x_147);
lean_ctor_set(x_153, 4, x_148);
lean_ctor_set(x_153, 5, x_149);
lean_ctor_set(x_153, 6, x_150);
lean_ctor_set_uint64(x_153, sizeof(void*)*7, x_143);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 8, x_144);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 9, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 10, x_152);
lean_inc(x_39);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_154 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_9, x_39, x_2, x_54, x_55, x_56, x_57, x_153, x_59, x_60, x_61, x_114);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_unbox(x_38);
lean_dec(x_38);
x_40 = x_37;
x_41 = x_157;
x_42 = x_155;
x_43 = x_156;
goto block_52;
}
else
{
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_ctor_get(x_154, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 1);
lean_inc(x_159);
lean_dec(x_154);
x_160 = lean_unbox(x_38);
lean_dec(x_38);
x_40 = x_37;
x_41 = x_160;
x_42 = x_158;
x_43 = x_159;
goto block_52;
}
else
{
uint8_t x_161; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_161 = !lean_is_exclusive(x_154);
if (x_161 == 0)
{
return x_154;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_154, 0);
x_163 = lean_ctor_get(x_154, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_154);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
case 2:
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_63, 1);
lean_inc(x_165);
lean_dec(x_63);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_39);
x_166 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_39, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; lean_object* x_188; uint8_t x_189; uint64_t x_190; lean_object* x_191; uint64_t x_192; uint64_t x_193; uint64_t x_194; uint8_t x_195; uint64_t x_196; uint64_t x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_box(2);
x_170 = lean_ctor_get(x_58, 0);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_170, 0);
x_172 = lean_ctor_get_uint8(x_170, 1);
x_173 = lean_ctor_get_uint8(x_170, 2);
x_174 = lean_ctor_get_uint8(x_170, 3);
x_175 = lean_ctor_get_uint8(x_170, 4);
x_176 = lean_ctor_get_uint8(x_170, 5);
x_177 = lean_ctor_get_uint8(x_170, 6);
x_178 = lean_ctor_get_uint8(x_170, 7);
x_179 = lean_ctor_get_uint8(x_170, 8);
x_180 = lean_ctor_get_uint8(x_170, 10);
x_181 = lean_ctor_get_uint8(x_170, 11);
x_182 = lean_ctor_get_uint8(x_170, 12);
x_183 = lean_ctor_get_uint8(x_170, 13);
x_184 = lean_ctor_get_uint8(x_170, 14);
x_185 = lean_ctor_get_uint8(x_170, 15);
x_186 = lean_ctor_get_uint8(x_170, 16);
x_187 = lean_ctor_get_uint8(x_170, 17);
lean_dec(x_170);
x_188 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_188, 0, x_171);
lean_ctor_set_uint8(x_188, 1, x_172);
lean_ctor_set_uint8(x_188, 2, x_173);
lean_ctor_set_uint8(x_188, 3, x_174);
lean_ctor_set_uint8(x_188, 4, x_175);
lean_ctor_set_uint8(x_188, 5, x_176);
lean_ctor_set_uint8(x_188, 6, x_177);
lean_ctor_set_uint8(x_188, 7, x_178);
lean_ctor_set_uint8(x_188, 8, x_179);
x_189 = lean_unbox(x_169);
lean_ctor_set_uint8(x_188, 9, x_189);
lean_ctor_set_uint8(x_188, 10, x_180);
lean_ctor_set_uint8(x_188, 11, x_181);
lean_ctor_set_uint8(x_188, 12, x_182);
lean_ctor_set_uint8(x_188, 13, x_183);
lean_ctor_set_uint8(x_188, 14, x_184);
lean_ctor_set_uint8(x_188, 15, x_185);
lean_ctor_set_uint8(x_188, 16, x_186);
lean_ctor_set_uint8(x_188, 17, x_187);
x_190 = lean_ctor_get_uint64(x_58, sizeof(void*)*7);
x_191 = lean_unsigned_to_nat(2u);
x_192 = lean_uint64_of_nat(x_191);
x_193 = lean_uint64_shift_right(x_190, x_192);
x_194 = lean_uint64_shift_left(x_193, x_192);
x_195 = lean_unbox(x_169);
x_196 = l_Lean_Meta_TransparencyMode_toUInt64(x_195);
x_197 = lean_uint64_lor(x_194, x_196);
x_198 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 8);
x_199 = lean_ctor_get(x_58, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_58, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_58, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_58, 4);
lean_inc(x_202);
x_203 = lean_ctor_get(x_58, 5);
lean_inc(x_203);
x_204 = lean_ctor_get(x_58, 6);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 9);
x_206 = lean_ctor_get_uint8(x_58, sizeof(void*)*7 + 10);
lean_dec(x_58);
x_207 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_207, 0, x_188);
lean_ctor_set(x_207, 1, x_199);
lean_ctor_set(x_207, 2, x_200);
lean_ctor_set(x_207, 3, x_201);
lean_ctor_set(x_207, 4, x_202);
lean_ctor_set(x_207, 5, x_203);
lean_ctor_set(x_207, 6, x_204);
lean_ctor_set_uint64(x_207, sizeof(void*)*7, x_197);
lean_ctor_set_uint8(x_207, sizeof(void*)*7 + 8, x_198);
lean_ctor_set_uint8(x_207, sizeof(void*)*7 + 9, x_205);
lean_ctor_set_uint8(x_207, sizeof(void*)*7 + 10, x_206);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_208 = l_Lean_Meta_Grind_Canon_canonElemCore(x_4, x_5, x_9, x_167, x_2, x_54, x_55, x_56, x_57, x_207, x_59, x_60, x_61, x_168);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_unbox(x_38);
lean_dec(x_38);
x_40 = x_37;
x_41 = x_211;
x_42 = x_209;
x_43 = x_210;
goto block_52;
}
else
{
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_212 = lean_ctor_get(x_208, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_208, 1);
lean_inc(x_213);
lean_dec(x_208);
x_214 = lean_unbox(x_38);
lean_dec(x_38);
x_40 = x_37;
x_41 = x_214;
x_42 = x_212;
x_43 = x_213;
goto block_52;
}
else
{
uint8_t x_215; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_215 = !lean_is_exclusive(x_208);
if (x_215 == 0)
{
return x_208;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_208, 0);
x_217 = lean_ctor_get(x_208, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_208);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_219 = !lean_is_exclusive(x_166);
if (x_219 == 0)
{
return x_166;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_166, 0);
x_221 = lean_ctor_get(x_166, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_166);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
default: 
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_63, 1);
lean_inc(x_223);
lean_dec(x_63);
lean_inc(x_39);
x_224 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_39, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_unbox(x_38);
lean_dec(x_38);
x_40 = x_37;
x_41 = x_227;
x_42 = x_225;
x_43 = x_226;
goto block_52;
}
else
{
uint8_t x_228; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_228 = !lean_is_exclusive(x_224);
if (x_228 == 0)
{
return x_224;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_224, 0);
x_230 = lean_ctor_get(x_224, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_224);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_232 = !lean_is_exclusive(x_63);
if (x_232 == 0)
{
return x_63;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_63, 0);
x_234 = lean_ctor_get(x_63, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_63);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_nat_add(x_9, x_22);
lean_dec(x_9);
x_24 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_20, x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
x_22 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6_spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
lean_dec(x_3);
x_53 = lean_array_set(x_4, x_5, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_5, x_54);
lean_dec(x_5);
x_3 = x_51;
x_4 = x_53;
x_5 = x_55;
goto _start;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_5);
x_57 = l_Lean_instInhabitedExpr;
x_124 = lean_mk_string_unchecked("Lean", 4, 4);
x_125 = lean_mk_string_unchecked("Grind", 5, 5);
x_126 = lean_mk_string_unchecked("nestedProof", 11, 11);
x_127 = l_Lean_Name_mkStr3(x_124, x_125, x_126);
x_128 = l_Lean_Expr_isConstOf(x_3, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
x_58 = x_128;
goto block_123;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_array_get_size(x_4);
x_130 = lean_unsigned_to_nat(2u);
x_131 = lean_nat_dec_eq(x_129, x_130);
lean_dec(x_129);
x_58 = x_131;
goto block_123;
}
block_123:
{
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
x_59 = l_Lean_Meta_getFunInfo(x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_array_get_size(x_4);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_box(x_58);
lean_inc(x_4);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_3);
lean_inc(x_2);
x_69 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(x_4, x_1, x_62, x_2, x_3, x_58, x_66, x_68, x_64, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_61);
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_4);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_dec(x_70);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_69, 0);
lean_dec(x_74);
lean_ctor_set(x_69, 0, x_2);
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
lean_dec(x_70);
x_80 = l_Lean_mkAppN(x_3, x_79);
lean_dec(x_79);
lean_ctor_set(x_69, 0, x_80);
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_dec(x_69);
x_82 = lean_ctor_get(x_70, 0);
lean_inc(x_82);
lean_dec(x_70);
x_83 = l_Lean_mkAppN(x_3, x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_69);
if (x_85 == 0)
{
return x_69;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_69, 0);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_69);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_59);
if (x_89 == 0)
{
return x_59;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_59, 0);
x_91 = lean_ctor_get(x_59, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_59);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_array_get(x_57, x_4, x_93);
lean_inc(x_7);
lean_inc(x_94);
x_95 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_94, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_st_ref_get(x_7, x_97);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_102, 2);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_mkAuxLemma_spec__0___redArg(x_103, x_96);
if (lean_obj_tag(x_104) == 0)
{
size_t x_105; size_t x_106; uint8_t x_107; 
lean_free_object(x_98);
x_105 = lean_ptr_addr(x_94);
lean_dec(x_94);
x_106 = lean_ptr_addr(x_96);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_2);
lean_inc(x_96);
x_108 = lean_array_set(x_4, x_93, x_96);
x_109 = l_Lean_mkAppN(x_3, x_108);
lean_dec(x_108);
x_16 = x_96;
x_17 = x_101;
x_18 = x_109;
goto block_50;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_96;
x_17 = x_101;
x_18 = x_2;
goto block_50;
}
}
else
{
lean_object* x_110; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
lean_dec(x_104);
lean_ctor_set(x_98, 0, x_110);
return x_98;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_98, 0);
x_112 = lean_ctor_get(x_98, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_98);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_113, 2);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_mkAuxLemma_spec__0___redArg(x_114, x_96);
if (lean_obj_tag(x_115) == 0)
{
size_t x_116; size_t x_117; uint8_t x_118; 
x_116 = lean_ptr_addr(x_94);
lean_dec(x_94);
x_117 = lean_ptr_addr(x_96);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_2);
lean_inc(x_96);
x_119 = lean_array_set(x_4, x_93, x_96);
x_120 = l_Lean_mkAppN(x_3, x_119);
lean_dec(x_119);
x_16 = x_96;
x_17 = x_112;
x_18 = x_120;
goto block_50;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_96;
x_17 = x_112;
x_18 = x_2;
goto block_50;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_121 = lean_ctor_get(x_115, 0);
lean_inc(x_121);
lean_dec(x_115);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_112);
return x_122;
}
}
}
else
{
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_95;
}
}
}
}
block_50:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_19 = lean_st_ref_take(x_7, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_18);
x_27 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_26, x_16, x_18);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_ctor_get(x_20, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_20, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_20, 7);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_20, sizeof(void*)*16);
x_36 = lean_ctor_get(x_20, 8);
lean_inc(x_36);
x_37 = lean_ctor_get(x_20, 9);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 10);
lean_inc(x_38);
x_39 = lean_ctor_get(x_20, 11);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 12);
lean_inc(x_40);
x_41 = lean_ctor_get(x_20, 13);
lean_inc(x_41);
x_42 = lean_ctor_get(x_20, 14);
lean_inc(x_42);
x_43 = lean_ctor_get(x_20, 15);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_30);
lean_ctor_set(x_44, 4, x_31);
lean_ctor_set(x_44, 5, x_32);
lean_ctor_set(x_44, 6, x_33);
lean_ctor_set(x_44, 7, x_34);
lean_ctor_set(x_44, 8, x_36);
lean_ctor_set(x_44, 9, x_37);
lean_ctor_set(x_44, 10, x_38);
lean_ctor_set(x_44, 11, x_39);
lean_ctor_set(x_44, 12, x_40);
lean_ctor_set(x_44, 13, x_41);
lean_ctor_set(x_44, 14, x_42);
lean_ctor_set(x_44, 15, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*16, x_35);
x_45 = lean_st_ref_set(x_7, x_44, x_21);
lean_dec(x_7);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_18);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
lean_dec(x_3);
x_53 = lean_array_set(x_4, x_5, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_5, x_54);
x_56 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6_spec__6(x_1, x_2, x_51, x_53, x_55, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_57 = l_Lean_instInhabitedExpr;
x_124 = lean_mk_string_unchecked("Lean", 4, 4);
x_125 = lean_mk_string_unchecked("Grind", 5, 5);
x_126 = lean_mk_string_unchecked("nestedProof", 11, 11);
x_127 = l_Lean_Name_mkStr3(x_124, x_125, x_126);
x_128 = l_Lean_Expr_isConstOf(x_3, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
x_58 = x_128;
goto block_123;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_array_get_size(x_4);
x_130 = lean_unsigned_to_nat(2u);
x_131 = lean_nat_dec_eq(x_129, x_130);
lean_dec(x_129);
x_58 = x_131;
goto block_123;
}
block_123:
{
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
x_59 = l_Lean_Meta_getFunInfo(x_3, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_array_get_size(x_4);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_box(x_58);
lean_inc(x_4);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_3);
lean_inc(x_2);
x_69 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(x_4, x_1, x_62, x_2, x_3, x_58, x_66, x_68, x_64, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_61);
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_4);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_dec(x_70);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_69, 0);
lean_dec(x_74);
lean_ctor_set(x_69, 0, x_2);
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
lean_dec(x_70);
x_80 = l_Lean_mkAppN(x_3, x_79);
lean_dec(x_79);
lean_ctor_set(x_69, 0, x_80);
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_dec(x_69);
x_82 = lean_ctor_get(x_70, 0);
lean_inc(x_82);
lean_dec(x_70);
x_83 = l_Lean_mkAppN(x_3, x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_69);
if (x_85 == 0)
{
return x_69;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_69, 0);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_69);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_59);
if (x_89 == 0)
{
return x_59;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_59, 0);
x_91 = lean_ctor_get(x_59, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_59);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_array_get(x_57, x_4, x_93);
lean_inc(x_7);
lean_inc(x_94);
x_95 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_94, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_st_ref_get(x_7, x_97);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_102, 2);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_mkAuxLemma_spec__0___redArg(x_103, x_96);
if (lean_obj_tag(x_104) == 0)
{
size_t x_105; size_t x_106; uint8_t x_107; 
lean_free_object(x_98);
x_105 = lean_ptr_addr(x_94);
lean_dec(x_94);
x_106 = lean_ptr_addr(x_96);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_2);
lean_inc(x_96);
x_108 = lean_array_set(x_4, x_93, x_96);
x_109 = l_Lean_mkAppN(x_3, x_108);
lean_dec(x_108);
x_16 = x_96;
x_17 = x_101;
x_18 = x_109;
goto block_50;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_96;
x_17 = x_101;
x_18 = x_2;
goto block_50;
}
}
else
{
lean_object* x_110; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
lean_dec(x_104);
lean_ctor_set(x_98, 0, x_110);
return x_98;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_98, 0);
x_112 = lean_ctor_get(x_98, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_98);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_113, 2);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_mkAuxLemma_spec__0___redArg(x_114, x_96);
if (lean_obj_tag(x_115) == 0)
{
size_t x_116; size_t x_117; uint8_t x_118; 
x_116 = lean_ptr_addr(x_94);
lean_dec(x_94);
x_117 = lean_ptr_addr(x_96);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_2);
lean_inc(x_96);
x_119 = lean_array_set(x_4, x_93, x_96);
x_120 = l_Lean_mkAppN(x_3, x_119);
lean_dec(x_119);
x_16 = x_96;
x_17 = x_112;
x_18 = x_120;
goto block_50;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
x_16 = x_96;
x_17 = x_112;
x_18 = x_2;
goto block_50;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_121 = lean_ctor_get(x_115, 0);
lean_inc(x_121);
lean_dec(x_115);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_112);
return x_122;
}
}
}
else
{
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_95;
}
}
}
}
block_50:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_19 = lean_st_ref_take(x_7, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_18);
x_27 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_26, x_16, x_18);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_ctor_get(x_20, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_20, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_20, 7);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_20, sizeof(void*)*16);
x_36 = lean_ctor_get(x_20, 8);
lean_inc(x_36);
x_37 = lean_ctor_get(x_20, 9);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 10);
lean_inc(x_38);
x_39 = lean_ctor_get(x_20, 11);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 12);
lean_inc(x_40);
x_41 = lean_ctor_get(x_20, 13);
lean_inc(x_41);
x_42 = lean_ctor_get(x_20, 14);
lean_inc(x_42);
x_43 = lean_ctor_get(x_20, 15);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_30);
lean_ctor_set(x_44, 4, x_31);
lean_ctor_set(x_44, 5, x_32);
lean_ctor_set(x_44, 6, x_33);
lean_ctor_set(x_44, 7, x_34);
lean_ctor_set(x_44, 8, x_36);
lean_ctor_set(x_44, 9, x_37);
lean_ctor_set(x_44, 10, x_38);
lean_ctor_set(x_44, 11, x_39);
lean_ctor_set(x_44, 12, x_40);
lean_ctor_set(x_44, 13, x_41);
lean_ctor_set(x_44, 14, x_42);
lean_ctor_set(x_44, 15, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*16, x_35);
x_45 = lean_st_ref_set(x_7, x_44, x_21);
lean_dec(x_7);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_18);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_16 = l_instMonadEIO(lean_box(0));
x_17 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, lean_box(0));
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_31, 0, x_30);
lean_inc(x_31);
lean_inc(x_28);
lean_inc(x_25);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_14);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_15);
x_34 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_25);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_28);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_31);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_12);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_43);
lean_ctor_set(x_46, 4, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_13);
x_48 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_47);
x_49 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_48);
x_50 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_49);
x_51 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_50);
x_52 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_51);
x_53 = l_Lean_instInhabitedExpr;
x_54 = l_instInhabitedOfMonad___redArg(x_52, x_53);
x_55 = lean_panic_fn(x_54, x_1);
x_56 = lean_apply_10(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_56;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_23; 
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; size_t x_40; size_t x_41; lean_object* x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; uint8_t x_47; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
x_26 = lean_array_get_size(x_25);
x_27 = lean_ptr_addr(x_1);
x_28 = lean_usize_to_uint64(x_27);
x_29 = lean_unsigned_to_nat(11u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_mix_hash(x_28, x_30);
x_32 = lean_unsigned_to_nat(32u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_unsigned_to_nat(16u);
x_37 = lean_uint64_of_nat(x_36);
x_38 = lean_uint64_shift_right(x_35, x_37);
x_39 = lean_uint64_xor(x_35, x_38);
x_40 = lean_uint64_to_usize(x_39);
x_41 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_usize_of_nat(x_42);
x_44 = lean_usize_sub(x_41, x_43);
x_45 = lean_usize_land(x_40, x_44);
x_46 = lean_array_uget(x_25, x_45);
x_47 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = lean_nat_add(x_24, x_42);
lean_dec(x_24);
lean_inc(x_2);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set(x_49, 2, x_46);
x_50 = lean_array_uset(x_25, x_45, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_shiftl(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_50);
lean_ctor_set(x_14, 1, x_57);
lean_ctor_set(x_14, 0, x_48);
x_16 = x_14;
goto block_22;
}
else
{
lean_ctor_set(x_14, 1, x_50);
lean_ctor_set(x_14, 0, x_48);
x_16 = x_14;
goto block_22;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_box(0);
x_59 = lean_array_uset(x_25, x_45, x_58);
lean_inc(x_2);
x_60 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(x_1, x_2, x_46);
x_61 = lean_array_uset(x_59, x_45, x_60);
lean_ctor_set(x_14, 1, x_61);
x_16 = x_14;
goto block_22;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; uint64_t x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; size_t x_78; size_t x_79; lean_object* x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_64 = lean_array_get_size(x_63);
x_65 = lean_ptr_addr(x_1);
x_66 = lean_usize_to_uint64(x_65);
x_67 = lean_unsigned_to_nat(11u);
x_68 = lean_uint64_of_nat(x_67);
x_69 = lean_uint64_mix_hash(x_66, x_68);
x_70 = lean_unsigned_to_nat(32u);
x_71 = lean_uint64_of_nat(x_70);
x_72 = lean_uint64_shift_right(x_69, x_71);
x_73 = lean_uint64_xor(x_69, x_72);
x_74 = lean_unsigned_to_nat(16u);
x_75 = lean_uint64_of_nat(x_74);
x_76 = lean_uint64_shift_right(x_73, x_75);
x_77 = lean_uint64_xor(x_73, x_76);
x_78 = lean_uint64_to_usize(x_77);
x_79 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_usize_of_nat(x_80);
x_82 = lean_usize_sub(x_79, x_81);
x_83 = lean_usize_land(x_78, x_82);
x_84 = lean_array_uget(x_63, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_86 = lean_nat_add(x_62, x_80);
lean_dec(x_62);
lean_inc(x_2);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_84);
x_88 = lean_array_uset(x_63, x_83, x_87);
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_nat_shiftl(x_86, x_89);
x_91 = lean_unsigned_to_nat(3u);
x_92 = lean_nat_div(x_90, x_91);
lean_dec(x_90);
x_93 = lean_array_get_size(x_88);
x_94 = lean_nat_dec_le(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_95);
x_16 = x_96;
goto block_22;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_86);
lean_ctor_set(x_97, 1, x_88);
x_16 = x_97;
goto block_22;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_box(0);
x_99 = lean_array_uset(x_63, x_83, x_98);
lean_inc(x_2);
x_100 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(x_1, x_2, x_84);
x_101 = lean_array_uset(x_99, x_83, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_62);
lean_ctor_set(x_102, 1, x_101);
x_16 = x_102;
goto block_22;
}
}
block_22:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_set(x_3, x_16, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_72; uint8_t x_190; 
x_190 = l_Lean_Expr_isApp(x_1);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = l_Lean_Expr_isForall(x_1);
x_72 = x_191;
goto block_189;
}
else
{
x_72 = x_190;
goto block_189;
}
block_35:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
x_29 = l_Lean_Expr_forallE___override(x_15, x_13, x_24, x_25);
x_30 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_29, x_17, x_21, x_19, x_27, x_12, x_14, x_22, x_20, x_18, x_16);
lean_dec(x_18);
lean_dec(x_20);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_21);
lean_dec(x_17);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_23, x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_32 = l_Lean_Expr_forallE___override(x_15, x_13, x_24, x_25);
x_33 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_32, x_17, x_21, x_19, x_27, x_12, x_14, x_22, x_20, x_18, x_16);
lean_dec(x_18);
lean_dec(x_20);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_21);
lean_dec(x_17);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_13);
x_34 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_26, x_17, x_21, x_19, x_27, x_12, x_14, x_22, x_20, x_18, x_16);
lean_dec(x_18);
lean_dec(x_20);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_27);
lean_dec(x_19);
lean_dec(x_21);
lean_dec(x_17);
return x_34;
}
}
}
block_71:
{
lean_object* x_52; 
x_52 = l_Lean_Expr_forallE___override(x_36, x_38, x_39, x_40);
if (lean_obj_tag(x_52) == 7)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; size_t x_57; size_t x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_52, sizeof(void*)*3 + 8);
x_57 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_58 = lean_ptr_addr(x_37);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_dec(x_55);
x_12 = x_46;
x_13 = x_37;
x_14 = x_47;
x_15 = x_53;
x_16 = x_51;
x_17 = x_42;
x_18 = x_50;
x_19 = x_44;
x_20 = x_49;
x_21 = x_43;
x_22 = x_48;
x_23 = x_56;
x_24 = x_41;
x_25 = x_40;
x_26 = x_52;
x_27 = x_45;
x_28 = x_59;
goto block_35;
}
else
{
size_t x_60; size_t x_61; uint8_t x_62; 
x_60 = lean_ptr_addr(x_55);
lean_dec(x_55);
x_61 = lean_ptr_addr(x_41);
x_62 = lean_usize_dec_eq(x_60, x_61);
x_12 = x_46;
x_13 = x_37;
x_14 = x_47;
x_15 = x_53;
x_16 = x_51;
x_17 = x_42;
x_18 = x_50;
x_19 = x_44;
x_20 = x_49;
x_21 = x_43;
x_22 = x_48;
x_23 = x_56;
x_24 = x_41;
x_25 = x_40;
x_26 = x_52;
x_27 = x_45;
x_28 = x_62;
goto block_35;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_52);
lean_dec(x_41);
lean_dec(x_37);
x_63 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_64 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_65 = lean_unsigned_to_nat(1828u);
x_66 = lean_unsigned_to_nat(23u);
x_67 = lean_mk_string_unchecked("forall expected", 15, 15);
x_68 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_63, x_64, x_65, x_66, x_67);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_63);
x_69 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_68);
x_70 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_69, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
return x_70;
}
}
block_189:
{
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_11);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_st_ref_get(x_2, x_11);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; size_t x_80; uint64_t x_81; lean_object* x_82; uint64_t x_83; uint64_t x_84; lean_object* x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; size_t x_93; size_t x_94; lean_object* x_95; size_t x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_array_get_size(x_78);
x_80 = lean_ptr_addr(x_1);
x_81 = lean_usize_to_uint64(x_80);
x_82 = lean_unsigned_to_nat(11u);
x_83 = lean_uint64_of_nat(x_82);
x_84 = lean_uint64_mix_hash(x_81, x_83);
x_85 = lean_unsigned_to_nat(32u);
x_86 = lean_uint64_of_nat(x_85);
x_87 = lean_uint64_shift_right(x_84, x_86);
x_88 = lean_uint64_xor(x_84, x_87);
x_89 = lean_unsigned_to_nat(16u);
x_90 = lean_uint64_of_nat(x_89);
x_91 = lean_uint64_shift_right(x_88, x_90);
x_92 = lean_uint64_xor(x_88, x_91);
x_93 = lean_uint64_to_usize(x_92);
x_94 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_usize_of_nat(x_95);
x_97 = lean_usize_sub(x_94, x_96);
x_98 = lean_usize_land(x_93, x_97);
x_99 = lean_array_uget(x_78, x_98);
lean_dec(x_78);
x_100 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(x_1, x_99);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_free_object(x_74);
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_box(0);
x_102 = l_Lean_Expr_sort___override(x_101);
x_103 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_103);
x_104 = lean_mk_array(x_103, x_102);
x_105 = lean_nat_sub(x_103, x_95);
lean_dec(x_103);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_n(x_1, 2);
x_106 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(x_72, x_1, x_1, x_104, x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_108);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_109;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_106;
}
}
case 7:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 2);
lean_inc(x_112);
x_113 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_111);
x_114 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Expr_hasLooseBVars(x_112);
if (x_117 == 0)
{
lean_object* x_118; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_112);
x_118 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_36 = x_110;
x_37 = x_115;
x_38 = x_111;
x_39 = x_112;
x_40 = x_113;
x_41 = x_119;
x_42 = x_2;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_120;
goto block_71;
}
else
{
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_118;
}
}
else
{
lean_inc(x_112);
x_36 = x_110;
x_37 = x_115;
x_38 = x_111;
x_39 = x_112;
x_40 = x_113;
x_41 = x_112;
x_42 = x_2;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_116;
goto block_71;
}
}
else
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_114;
}
}
default: 
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Canon", 28, 28);
x_122 = lean_mk_string_unchecked("Lean.Meta.Grind.Canon.canonImpl.visit", 37, 37);
x_123 = lean_unsigned_to_nat(192u);
x_124 = lean_unsigned_to_nat(13u);
x_125 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_126 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_121, x_122, x_123, x_124, x_125);
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_121);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_127 = l_panic___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__8(x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_129);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_130;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_127;
}
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_ctor_get(x_100, 0);
lean_inc(x_131);
lean_dec(x_100);
lean_ctor_set(x_74, 0, x_131);
return x_74;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; size_t x_136; uint64_t x_137; lean_object* x_138; uint64_t x_139; uint64_t x_140; lean_object* x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; lean_object* x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; size_t x_149; size_t x_150; lean_object* x_151; size_t x_152; size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; 
x_132 = lean_ctor_get(x_74, 0);
x_133 = lean_ctor_get(x_74, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_74);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_array_get_size(x_134);
x_136 = lean_ptr_addr(x_1);
x_137 = lean_usize_to_uint64(x_136);
x_138 = lean_unsigned_to_nat(11u);
x_139 = lean_uint64_of_nat(x_138);
x_140 = lean_uint64_mix_hash(x_137, x_139);
x_141 = lean_unsigned_to_nat(32u);
x_142 = lean_uint64_of_nat(x_141);
x_143 = lean_uint64_shift_right(x_140, x_142);
x_144 = lean_uint64_xor(x_140, x_143);
x_145 = lean_unsigned_to_nat(16u);
x_146 = lean_uint64_of_nat(x_145);
x_147 = lean_uint64_shift_right(x_144, x_146);
x_148 = lean_uint64_xor(x_144, x_147);
x_149 = lean_uint64_to_usize(x_148);
x_150 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_usize_of_nat(x_151);
x_153 = lean_usize_sub(x_150, x_152);
x_154 = lean_usize_land(x_149, x_153);
x_155 = lean_array_uget(x_134, x_154);
lean_dec(x_134);
x_156 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(x_1, x_155);
lean_dec(x_155);
if (lean_obj_tag(x_156) == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_box(0);
x_158 = l_Lean_Expr_sort___override(x_157);
x_159 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_159);
x_160 = lean_mk_array(x_159, x_158);
x_161 = lean_nat_sub(x_159, x_151);
lean_dec(x_159);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_n(x_1, 2);
x_162 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(x_72, x_1, x_1, x_160, x_161, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_133);
lean_dec(x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_164);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_165;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_162;
}
}
case 7:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_1, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_1, 2);
lean_inc(x_168);
x_169 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_167);
x_170 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_133);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Expr_hasLooseBVars(x_168);
if (x_173 == 0)
{
lean_object* x_174; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_168);
x_174 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_36 = x_166;
x_37 = x_171;
x_38 = x_167;
x_39 = x_168;
x_40 = x_169;
x_41 = x_175;
x_42 = x_2;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_176;
goto block_71;
}
else
{
lean_dec(x_171);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_174;
}
}
else
{
lean_inc(x_168);
x_36 = x_166;
x_37 = x_171;
x_38 = x_167;
x_39 = x_168;
x_40 = x_169;
x_41 = x_168;
x_42 = x_2;
x_43 = x_3;
x_44 = x_4;
x_45 = x_5;
x_46 = x_6;
x_47 = x_7;
x_48 = x_8;
x_49 = x_9;
x_50 = x_10;
x_51 = x_172;
goto block_71;
}
}
else
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_170;
}
}
default: 
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_177 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Canon", 28, 28);
x_178 = lean_mk_string_unchecked("Lean.Meta.Grind.Canon.canonImpl.visit", 37, 37);
x_179 = lean_unsigned_to_nat(192u);
x_180 = lean_unsigned_to_nat(13u);
x_181 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_182 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_177, x_178, x_179, x_180, x_181);
lean_dec(x_181);
lean_dec(x_178);
lean_dec(x_177);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_183 = l_panic___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__8(x_182, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_133);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_184, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_185);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_186;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_183;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_ctor_get(x_156, 0);
lean_inc(x_187);
lean_dec(x_156);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_133);
return x_188;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___redArg___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_1);
lean_dec(x_1);
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___redArg(x_19, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
lean_dec(x_2);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_unbox(x_2);
lean_dec(x_2);
x_23 = lean_unbox(x_6);
lean_dec(x_6);
x_24 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3_spec__3(x_1, x_22, x_3, x_4, x_5, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_2);
lean_dec(x_2);
x_21 = lean_unbox(x_6);
lean_dec(x_6);
x_22 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(x_1, x_20, x_3, x_4, x_5, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_unbox(x_2);
lean_dec(x_2);
x_23 = lean_unbox(x_6);
lean_dec(x_6);
x_24 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__3(x_1, x_22, x_3, x_4, x_5, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6_spec__6(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Canon_canonImpl_visit___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(64u);
x_12 = l_Lean_mkPtrMap(lean_box(0), lean_box(0), x_11);
x_13 = lean_st_mk_ref(x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Meta_Grind_Canon_canonImpl_visit(x_1, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_dec(x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_canon(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_mk_string_unchecked("grind", 5, 5);
x_12 = lean_mk_string_unchecked("debug", 5, 5);
x_13 = lean_mk_string_unchecked("canon", 5, 5);
x_14 = l_Lean_Name_mkStr3(x_11, x_12, x_13);
lean_inc(x_14);
x_15 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_14, x_8, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
lean_inc(x_1);
x_27 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_26);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_27);
lean_ctor_set(x_15, 0, x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_14, x_28, x_6, x_7, x_8, x_9, x_24);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_free_object(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_dec(x_15);
x_37 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_mk_string_unchecked("", 0, 0);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
lean_inc(x_1);
x_41 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_14, x_43, x_6, x_7, x_8, x_9, x_38);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Meta_Grind_Canon_canonImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_49 = x_37;
} else {
 lean_dec_ref(x_37);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FVarSubset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FVarSubset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FVarSubset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FVarSubset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult = _init_l_Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult();
l_Lean_Meta_Grind_Canon_instReprShouldCanonResult = _init_l_Lean_Meta_Grind_Canon_instReprShouldCanonResult();
lean_mark_persistent(l_Lean_Meta_Grind_Canon_instReprShouldCanonResult);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
