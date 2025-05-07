// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MatchCond
// Imports: Init.Grind Init.Simproc Lean.Meta.Tactic.Contradiction Lean.Meta.Tactic.Grind.ProveEq Lean.Meta.Tactic.Grind.PropagatorAttr
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object**);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1____x40_Lean_Meta_Tactic_Grind_MatchCond___hyg_11153_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_getRootENode_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at_____private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object**);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1____x40_Lean_Meta_Tactic_Grind_MatchCond___hyg_11235_(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object**);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_8);
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_13 = lean_mk_string_unchecked("Eq", 2, 2);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Expr_isConstOf(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = l_Lean_Expr_isApp(x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_12);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_19 = lean_mk_string_unchecked("HEq", 3, 3);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Lean_Expr_isConstOf(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_11);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_8);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_11);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(0);
x_13 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_5);
if (lean_obj_tag(x_13) == 0)
{
x_8 = x_4;
goto block_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
x_20 = l_Lean_Expr_hasLooseBVars(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_ctor_set(x_15, 1, x_16);
x_21 = lean_array_push(x_4, x_15);
x_8 = x_21;
goto block_12;
}
else
{
lean_free_object(x_15);
lean_dec(x_18);
lean_dec(x_16);
x_8 = x_4;
goto block_12;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Expr_hasLooseBVars(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_16);
x_25 = lean_array_push(x_4, x_24);
x_8 = x_25;
goto block_12;
}
else
{
lean_dec(x_22);
lean_dec(x_16);
x_8 = x_4;
goto block_12;
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_1 = x_10;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_cleanupAnnotations(x_1);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_7 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_8 = l_Lean_Expr_isApp(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc(x_7);
x_10 = l_Lean_Expr_appFnCleanup___redArg(x_7);
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_17 = lean_mk_string_unchecked("Eq", 2, 2);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = l_Lean_Expr_isConstOf(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isApp(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_27 = lean_mk_string_unchecked("HEq", 3, 3);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Expr_isConstOf(x_22, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l_Lean_Expr_hasLooseBVars(x_15);
lean_dec(x_15);
if (x_31 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_33 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_34 = lean_unsigned_to_nat(21u);
x_35 = lean_unsigned_to_nat(14u);
x_36 = lean_mk_string_unchecked("value is none", 13, 13);
x_37 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_32, x_33, x_34, x_35, x_36);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
x_38 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_37);
x_23 = x_38;
goto block_26;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec(x_3);
x_23 = x_39;
goto block_26;
}
}
else
{
lean_object* x_40; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
return x_40;
}
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_mkApp4(x_22, x_23, x_2, x_14, x_13);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_3);
x_41 = l_Lean_Expr_hasLooseBVars(x_14);
lean_dec(x_14);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_mkApp3(x_16, x_15, x_2, x_13);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
x_44 = lean_box(0);
return x_44;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = lean_array_fget(x_1, x_4);
x_12 = lean_box(0);
x_13 = lean_array_get(x_12, x_2, x_4);
lean_inc(x_6);
x_14 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(x_6, x_11, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Expr_forallE___override(x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; size_t x_26; size_t x_27; uint8_t x_28; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 8);
x_20 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(x_1, x_2, x_7, x_4);
x_26 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_27 = lean_ptr_addr(x_6);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_18);
x_21 = x_28;
goto block_25;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_30 = lean_ptr_addr(x_20);
x_31 = lean_usize_dec_eq(x_29, x_30);
x_21 = x_31;
goto block_25;
}
block_25:
{
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_15);
x_22 = l_Lean_Expr_forallE___override(x_16, x_6, x_20, x_8);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_19, x_8);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_15);
x_24 = l_Lean_Expr_forallE___override(x_16, x_6, x_20, x_8);
return x_24;
}
else
{
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_6);
return x_15;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
x_32 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_33 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_34 = lean_unsigned_to_nat(1828u);
x_35 = lean_unsigned_to_nat(23u);
x_36 = lean_mk_string_unchecked("forall expected", 15, 15);
x_37 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_32, x_33, x_34, x_35, x_36);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_32);
x_38 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_41 = l_Lean_Expr_forallE___override(x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 7)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; size_t x_53; size_t x_54; uint8_t x_55; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
x_46 = lean_nat_add(x_4, x_40);
x_47 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(x_1, x_2, x_7, x_46);
lean_dec(x_46);
x_53 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_54 = lean_ptr_addr(x_39);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_dec(x_44);
x_48 = x_55;
goto block_52;
}
else
{
size_t x_56; size_t x_57; uint8_t x_58; 
x_56 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_57 = lean_ptr_addr(x_47);
x_58 = lean_usize_dec_eq(x_56, x_57);
x_48 = x_58;
goto block_52;
}
block_52:
{
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_41);
x_49 = l_Lean_Expr_forallE___override(x_42, x_39, x_47, x_8);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_45, x_8);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_41);
x_51 = l_Lean_Expr_forallE___override(x_42, x_39, x_47, x_8);
return x_51;
}
else
{
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_39);
return x_41;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_7);
x_59 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_60 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_61 = lean_unsigned_to_nat(1828u);
x_62 = lean_unsigned_to_nat(23u);
x_63 = lean_mk_string_unchecked("forall expected", 15, 15);
x_64 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_59, x_60, x_61, x_62, x_63);
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_59);
x_65 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_64);
return x_65;
}
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
lean_inc(x_10);
x_22 = lean_array_push(x_2, x_10);
x_23 = lean_array_push(x_3, x_4);
x_24 = lean_array_push(x_5, x_10);
x_25 = lean_array_push(x_6, x_7);
x_26 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(x_8, x_9, x_21, x_22, x_23, x_24, x_25, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
lean_inc(x_11);
x_23 = lean_array_push(x_2, x_11);
lean_inc(x_3);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_3);
x_25 = lean_array_push(x_4, x_24);
x_26 = lean_array_push(x_5, x_3);
x_27 = lean_array_push(x_26, x_11);
x_28 = lean_array_push(x_6, x_7);
x_29 = lean_array_push(x_28, x_8);
x_30 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(x_9, x_10, x_22, x_23, x_25, x_27, x_29, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_10);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed), 20, 10);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_10);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_8);
lean_closure_set(x_20, 9, x_9);
x_21 = lean_mk_string_unchecked("x", 1, 1);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_name_append_index_after(x_22, x_1);
x_24 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__0(lean_box(0), x_23, x_10, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_2);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(x_4, x_5, x_1, x_19);
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_box(1);
x_22 = lean_box(1);
x_23 = lean_unbox(x_21);
x_24 = lean_unbox(x_22);
x_25 = l_Lean_Meta_mkLambdaFVars(x_6, x_20, x_18, x_23, x_18, x_24, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_mkAppN(x_26, x_7);
x_29 = l_Lean_Meta_Grind_shareCommon___redArg(x_28, x_11, x_27);
lean_dec(x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_7);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_array_fget(x_2, x_3);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_43);
x_44 = lean_infer_type(x_43, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_3);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed), 19, 9);
lean_closure_set(x_47, 0, x_3);
lean_closure_set(x_47, 1, x_4);
lean_closure_set(x_47, 2, x_5);
lean_closure_set(x_47, 3, x_42);
lean_closure_set(x_47, 4, x_6);
lean_closure_set(x_47, 5, x_7);
lean_closure_set(x_47, 6, x_43);
lean_closure_set(x_47, 7, x_1);
lean_closure_set(x_47, 8, x_2);
x_48 = lean_mk_string_unchecked("x", 1, 1);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = lean_name_append_index_after(x_49, x_3);
x_51 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__0(lean_box(0), x_50, x_45, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_46);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
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
x_52 = !lean_is_exclusive(x_44);
if (x_52 == 0)
{
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
lean_dec(x_41);
x_57 = lean_ctor_get(x_42, 0);
lean_inc(x_57);
lean_dec(x_42);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_57);
x_58 = lean_infer_type(x_57, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_3);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed), 19, 9);
lean_closure_set(x_61, 0, x_3);
lean_closure_set(x_61, 1, x_4);
lean_closure_set(x_61, 2, x_5);
lean_closure_set(x_61, 3, x_6);
lean_closure_set(x_61, 4, x_7);
lean_closure_set(x_61, 5, x_57);
lean_closure_set(x_61, 6, x_56);
lean_closure_set(x_61, 7, x_1);
lean_closure_set(x_61, 8, x_2);
x_62 = lean_mk_string_unchecked("ty", 2, 2);
x_63 = l_Lean_Name_mkStr1(x_62);
x_64 = lean_name_append_index_after(x_63, x_3);
x_65 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__0(lean_box(0), x_64, x_59, x_61, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_60);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
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
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_58);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object** _args) {
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
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_21; 
x_21 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object** _args) {
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
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_17; uint8_t x_18; 
lean_inc(x_1);
x_17 = l_Lean_Expr_cleanupAnnotations(x_1);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = lean_mk_string_unchecked("Lean", 4, 4);
x_21 = lean_mk_string_unchecked("Grind", 5, 5);
x_22 = lean_mk_string_unchecked("MatchCond", 9, 9);
x_23 = l_Lean_Name_mkStr3(x_20, x_21, x_22);
x_24 = l_Lean_Expr_isConstOf(x_19, x_23);
lean_dec(x_23);
lean_dec(x_19);
if (x_24 == 0)
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
lean_inc(x_25);
x_26 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_mk_empty_array_with_capacity(x_27);
lean_inc_n(x_28, 3);
x_29 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(x_25, x_26, x_27, x_28, x_28, x_28, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_29;
}
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = l_Lean_Expr_getAppNumArgs(x_2);
x_17 = lean_box(0);
x_18 = l_Lean_Expr_sort___override(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_nat_dec_lt(x_6, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_inc(x_16);
x_23 = lean_mk_array(x_16, x_18);
x_24 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
lean_inc(x_2);
x_25 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_23, x_24);
x_26 = l_Lean_instInhabitedExpr;
x_27 = lean_array_get(x_26, x_1, x_6);
x_28 = lean_array_get(x_26, x_25, x_6);
lean_dec(x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_29 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(x_27, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_box(0);
x_34 = lean_unbox(x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_ctor_get(x_4, 2);
x_38 = lean_nat_add(x_6, x_37);
lean_dec(x_6);
x_5 = x_36;
x_6 = x_38;
x_15 = x_32;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
x_40 = lean_box(x_3);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
lean_ctor_set(x_29, 0, x_42);
return x_29;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_box(0);
x_46 = lean_unbox(x_43);
lean_dec(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_ctor_get(x_4, 2);
x_50 = lean_nat_add(x_6, x_49);
lean_dec(x_6);
x_5 = x_48;
x_6 = x_50;
x_15 = x_44;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
x_52 = lean_box(x_3);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_45);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_44);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_29);
if (x_56 == 0)
{
return x_29;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_29, 0);
x_58 = lean_ctor_get(x_29, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_29);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_getRootENode___redArg(x_1, x_3, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*13 + 2);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*13 + 1);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(x_16);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_13, 1);
x_25 = lean_ctor_get(x_13, 0);
lean_dec(x_25);
x_26 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
lean_free_object(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_27 = l_Lean_Meta_isLitValue(x_2, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_32 = l_Lean_Meta_normLitValue(x_31, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_normLitValue(x_2, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_expr_eqv(x_33, x_37);
lean_dec(x_37);
lean_dec(x_33);
if (x_38 == 0)
{
lean_ctor_set(x_35, 0, x_28);
return x_35;
}
else
{
lean_object* x_39; 
lean_dec(x_28);
x_39 = lean_box(x_26);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_expr_eqv(x_33, x_40);
lean_dec(x_40);
lean_dec(x_33);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_28);
x_44 = lean_box(x_26);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_33);
lean_dec(x_28);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
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
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
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
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_27;
}
}
else
{
lean_object* x_54; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_54 = lean_box(x_15);
lean_ctor_set(x_13, 0, x_54);
return x_13;
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_dec(x_13);
x_56 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_56 == 0)
{
lean_object* x_57; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_57 = l_Lean_Meta_isLitValue(x_2, x_7, x_8, x_9, x_10, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
lean_dec(x_58);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_14, 0);
lean_inc(x_61);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_62 = l_Lean_Meta_normLitValue(x_61, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_normLitValue(x_2, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_expr_eqv(x_63, x_66);
lean_dec(x_66);
lean_dec(x_63);
if (x_69 == 0)
{
lean_object* x_70; 
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_58);
x_71 = lean_box(x_56);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
lean_dec(x_58);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_77 = lean_ctor_get(x_62, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_79 = x_62;
} else {
 lean_dec_ref(x_62);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_57;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_81 = lean_box(x_15);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_55);
return x_82;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_13, 1);
lean_inc(x_83);
lean_dec(x_13);
x_84 = lean_ctor_get(x_14, 0);
lean_inc(x_84);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_84);
x_85 = l_Lean_Meta_isConstructorApp_x3f(x_84, x_7, x_8, x_9, x_10, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_84);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 0);
lean_dec(x_88);
x_89 = lean_box(x_12);
lean_ctor_set(x_85, 0, x_89);
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_box(x_12);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_dec(x_85);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec(x_86);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_95 = l_Lean_Meta_isConstructorApp_x3f(x_2, x_7, x_8, x_9, x_10, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
lean_dec(x_94);
lean_dec(x_84);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
x_99 = lean_box(x_12);
lean_ctor_set(x_95, 0, x_99);
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_box(x_12);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_95);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; 
x_104 = lean_ctor_get(x_95, 1);
x_105 = lean_ctor_get(x_95, 0);
lean_dec(x_105);
x_106 = lean_ctor_get(x_96, 0);
lean_inc(x_106);
lean_dec(x_96);
x_107 = lean_ctor_get(x_94, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_name_eq(x_108, x_110);
lean_dec(x_110);
lean_dec(x_108);
x_112 = l_instDecidableNot___redArg(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_free_object(x_95);
x_113 = lean_box(0);
x_114 = l_Lean_Expr_sort___override(x_113);
x_115 = l_Lean_Expr_getAppNumArgs(x_84);
lean_inc(x_115);
x_116 = lean_mk_array(x_115, x_114);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_sub(x_115, x_117);
lean_dec(x_115);
x_119 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_84, x_116, x_118);
x_120 = lean_ctor_get(x_94, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_94, 4);
lean_inc(x_121);
lean_dec(x_94);
x_122 = lean_nat_add(x_120, x_121);
lean_dec(x_121);
lean_inc(x_120);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_117);
x_124 = lean_box(0);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_119, x_2, x_15, x_123, x_126, x_120, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_104);
lean_dec(x_123);
lean_dec(x_119);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec(x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_127);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_127, 0);
lean_dec(x_131);
x_132 = lean_box(x_12);
lean_ctor_set(x_127, 0, x_132);
return x_127;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
lean_dec(x_127);
x_134 = lean_box(x_12);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_127);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_127, 0);
lean_dec(x_137);
x_138 = lean_ctor_get(x_129, 0);
lean_inc(x_138);
lean_dec(x_129);
lean_ctor_set(x_127, 0, x_138);
return x_127;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_127, 1);
lean_inc(x_139);
lean_dec(x_127);
x_140 = lean_ctor_get(x_129, 0);
lean_inc(x_140);
lean_dec(x_129);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_127);
if (x_142 == 0)
{
return x_127;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_127, 0);
x_144 = lean_ctor_get(x_127, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_127);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_94);
lean_dec(x_84);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_146 = lean_box(x_15);
lean_ctor_set(x_95, 0, x_146);
return x_95;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; 
x_147 = lean_ctor_get(x_95, 1);
lean_inc(x_147);
lean_dec(x_95);
x_148 = lean_ctor_get(x_96, 0);
lean_inc(x_148);
lean_dec(x_96);
x_149 = lean_ctor_get(x_94, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_name_eq(x_150, x_152);
lean_dec(x_152);
lean_dec(x_150);
x_154 = l_instDecidableNot___redArg(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_155 = lean_box(0);
x_156 = l_Lean_Expr_sort___override(x_155);
x_157 = l_Lean_Expr_getAppNumArgs(x_84);
lean_inc(x_157);
x_158 = lean_mk_array(x_157, x_156);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_sub(x_157, x_159);
lean_dec(x_157);
x_161 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_84, x_158, x_160);
x_162 = lean_ctor_get(x_94, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_94, 4);
lean_inc(x_163);
lean_dec(x_94);
x_164 = lean_nat_add(x_162, x_163);
lean_dec(x_163);
lean_inc(x_162);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_159);
x_166 = lean_box(0);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_161, x_2, x_15, x_165, x_168, x_162, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_147);
lean_dec(x_165);
lean_dec(x_161);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec(x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_173 = x_169;
} else {
 lean_dec_ref(x_169);
 x_173 = lean_box(0);
}
x_174 = lean_box(x_12);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_169, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_177 = x_169;
} else {
 lean_dec_ref(x_169);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_171, 0);
lean_inc(x_178);
lean_dec(x_171);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_169, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_169, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_182 = x_169;
} else {
 lean_dec_ref(x_169);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_94);
lean_dec(x_84);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_184 = lean_box(x_15);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_147);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_94);
lean_dec(x_84);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_186 = !lean_is_exclusive(x_95);
if (x_186 == 0)
{
return x_95;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_95, 0);
x_188 = lean_ctor_get(x_95, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_95);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_84);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_190 = !lean_is_exclusive(x_85);
if (x_190 == 0)
{
return x_85;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_85, 0);
x_192 = lean_ctor_get(x_85, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_85);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_194 = !lean_is_exclusive(x_13);
if (x_194 == 0)
{
return x_13;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_13, 0);
x_196 = lean_ctor_get(x_13, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_13);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_11);
return x_199;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args) {
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
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(x_1, x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_13);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_21);
x_2 = x_26;
x_11 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_mk_string_unchecked("grind", 5, 5);
x_30 = lean_mk_string_unchecked("debug", 5, 5);
x_31 = lean_mk_string_unchecked("matchCond", 9, 9);
x_32 = l_Lean_Name_mkStr3(x_29, x_30, x_31);
lean_inc(x_32);
x_33 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_32, x_9, x_28);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_14 = x_36;
goto block_19;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
x_40 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_mk_string_unchecked("satifised", 9, 9);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
lean_inc(x_13);
x_44 = l_Lean_indentExpr(x_13);
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_43);
x_45 = lean_mk_string_unchecked("\nthe following equality is false", 32, 32);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_indentExpr(x_20);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("", 0, 0);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_32, x_52, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_14 = x_54;
goto block_19;
}
else
{
uint8_t x_55; 
lean_free_object(x_33);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_55 = !lean_is_exclusive(x_40);
if (x_55 == 0)
{
return x_40;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_40, 0);
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_40);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_33, 1);
lean_inc(x_59);
lean_dec(x_33);
x_60 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked("satifised", 9, 9);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
lean_inc(x_13);
x_64 = l_Lean_indentExpr(x_13);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_mk_string_unchecked("\nthe following equality is false", 32, 32);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_indentExpr(x_20);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked("", 0, 0);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_32, x_73, x_7, x_8, x_9, x_10, x_61);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_14 = x_75;
goto block_19;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = lean_ctor_get(x_60, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_60, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_78 = x_60;
} else {
 lean_dec_ref(x_60);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = !lean_is_exclusive(x_22);
if (x_80 == 0)
{
return x_22;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_22, 0);
x_82 = lean_ctor_get(x_22, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_22);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_13);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_11);
return x_85;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_13);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_21);
x_27 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0_spec__0(x_1, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_mk_string_unchecked("grind", 5, 5);
x_30 = lean_mk_string_unchecked("debug", 5, 5);
x_31 = lean_mk_string_unchecked("matchCond", 9, 9);
x_32 = l_Lean_Name_mkStr3(x_29, x_30, x_31);
lean_inc(x_32);
x_33 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_32, x_9, x_28);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_14 = x_36;
goto block_19;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
x_40 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_mk_string_unchecked("satifised", 9, 9);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
lean_inc(x_13);
x_44 = l_Lean_indentExpr(x_13);
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_43);
x_45 = lean_mk_string_unchecked("\nthe following equality is false", 32, 32);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_indentExpr(x_20);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("", 0, 0);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_32, x_52, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_14 = x_54;
goto block_19;
}
else
{
uint8_t x_55; 
lean_free_object(x_33);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_55 = !lean_is_exclusive(x_40);
if (x_55 == 0)
{
return x_40;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_40, 0);
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_40);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_33, 1);
lean_inc(x_59);
lean_dec(x_33);
x_60 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked("satifised", 9, 9);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
lean_inc(x_13);
x_64 = l_Lean_indentExpr(x_13);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_mk_string_unchecked("\nthe following equality is false", 32, 32);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_indentExpr(x_20);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked("", 0, 0);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_32, x_73, x_7, x_8, x_9, x_10, x_61);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_14 = x_75;
goto block_19;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = lean_ctor_get(x_60, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_60, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_78 = x_60;
} else {
 lean_dec_ref(x_60);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = !lean_is_exclusive(x_22);
if (x_80 == 0)
{
return x_22;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_22, 0);
x_82 = lean_ctor_get(x_22, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_22);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_12);
lean_ctor_set(x_84, 1, x_13);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_11);
return x_85;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; uint8_t x_19; 
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_18 = l_Lean_Expr_cleanupAnnotations(x_12);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_inc(x_18);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("Grind", 5, 5);
x_23 = lean_mk_string_unchecked("MatchCond", 9, 9);
x_24 = l_Lean_Name_mkStr3(x_21, x_22, x_23);
x_25 = l_Lean_Expr_isConstOf(x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
if (x_25 == 0)
{
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0(x_25, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_7, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_20 = lean_array_uget(x_5, x_7);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(x_1, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_7, x_28);
x_7 = x_29;
x_8 = x_26;
x_17 = x_23;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_box(0);
x_34 = lean_box(1);
x_35 = lean_unbox(x_33);
x_36 = lean_unbox(x_33);
x_37 = lean_unbox(x_34);
x_38 = l_Lean_Meta_mkLambdaFVars(x_2, x_32, x_35, x_3, x_36, x_37, x_13, x_14, x_15, x_16, x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_Lean_Expr_app___override(x_4, x_40);
lean_ctor_set(x_22, 0, x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_22);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_24);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = l_Lean_Expr_app___override(x_4, x_44);
lean_ctor_set(x_22, 0, x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_22);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_24);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_free_object(x_22);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
return x_38;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_22, 0);
lean_inc(x_54);
lean_dec(x_22);
x_55 = lean_box(0);
x_56 = lean_box(1);
x_57 = lean_unbox(x_55);
x_58 = lean_unbox(x_55);
x_59 = lean_unbox(x_56);
x_60 = l_Lean_Meta_mkLambdaFVars(x_2, x_54, x_57, x_3, x_58, x_59, x_13, x_14, x_15, x_16, x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = l_Lean_Expr_app___override(x_4, x_61);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_24);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_63;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
x_69 = lean_ctor_get(x_60, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_71 = x_60;
} else {
 lean_dec_ref(x_60);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_21);
if (x_73 == 0)
{
return x_21;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_21, 0);
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_21);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_apply_11(x_1, x_6, x_7, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0), 12, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_4);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_6);
lean_closure_set(x_13, 4, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___redArg(x_1, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_size(x_4);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(x_1, x_4, x_2, x_3, x_4, x_18, x_20, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_46; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; 
x_601 = lean_mk_string_unchecked("grind", 5, 5);
x_602 = lean_mk_string_unchecked("debug", 5, 5);
x_603 = lean_mk_string_unchecked("matchCond", 9, 9);
x_604 = l_Lean_Name_mkStr3(x_601, x_602, x_603);
lean_inc(x_604);
x_605 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_604, x_9, x_11);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_unbox(x_606);
lean_dec(x_606);
if (x_607 == 0)
{
lean_object* x_608; 
lean_dec(x_604);
x_608 = lean_ctor_get(x_605, 1);
lean_inc(x_608);
lean_dec(x_605);
x_222 = x_3;
x_223 = x_4;
x_224 = x_5;
x_225 = x_6;
x_226 = x_7;
x_227 = x_8;
x_228 = x_9;
x_229 = x_10;
x_230 = x_608;
goto block_600;
}
else
{
uint8_t x_609; 
x_609 = !lean_is_exclusive(x_605);
if (x_609 == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_605, 1);
x_611 = lean_ctor_get(x_605, 0);
lean_dec(x_611);
x_612 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_610);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; 
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_614 = lean_infer_type(x_2, x_7, x_8, x_9, x_10, x_613);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_mk_string_unchecked("go\?: ", 5, 5);
x_618 = l_Lean_stringToMessageData(x_617);
lean_dec(x_617);
x_619 = l_Lean_MessageData_ofExpr(x_615);
lean_ctor_set_tag(x_605, 7);
lean_ctor_set(x_605, 1, x_619);
lean_ctor_set(x_605, 0, x_618);
x_620 = lean_mk_string_unchecked("", 0, 0);
x_621 = l_Lean_stringToMessageData(x_620);
lean_dec(x_620);
x_622 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_622, 0, x_605);
lean_ctor_set(x_622, 1, x_621);
x_623 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_604, x_622, x_7, x_8, x_9, x_10, x_616);
x_624 = lean_ctor_get(x_623, 1);
lean_inc(x_624);
lean_dec(x_623);
x_222 = x_3;
x_223 = x_4;
x_224 = x_5;
x_225 = x_6;
x_226 = x_7;
x_227 = x_8;
x_228 = x_9;
x_229 = x_10;
x_230 = x_624;
goto block_600;
}
else
{
uint8_t x_625; 
lean_free_object(x_605);
lean_dec(x_604);
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
x_625 = !lean_is_exclusive(x_614);
if (x_625 == 0)
{
return x_614;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_614, 0);
x_627 = lean_ctor_get(x_614, 1);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_614);
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
return x_628;
}
}
}
else
{
uint8_t x_629; 
lean_free_object(x_605);
lean_dec(x_604);
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
x_629 = !lean_is_exclusive(x_612);
if (x_629 == 0)
{
return x_612;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_612, 0);
x_631 = lean_ctor_get(x_612, 1);
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_612);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_630);
lean_ctor_set(x_632, 1, x_631);
return x_632;
}
}
}
else
{
lean_object* x_633; lean_object* x_634; 
x_633 = lean_ctor_get(x_605, 1);
lean_inc(x_633);
lean_dec(x_605);
x_634 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_633);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; 
x_635 = lean_ctor_get(x_634, 1);
lean_inc(x_635);
lean_dec(x_634);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_636 = lean_infer_type(x_2, x_7, x_8, x_9, x_10, x_635);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_636, 1);
lean_inc(x_638);
lean_dec(x_636);
x_639 = lean_mk_string_unchecked("go\?: ", 5, 5);
x_640 = l_Lean_stringToMessageData(x_639);
lean_dec(x_639);
x_641 = l_Lean_MessageData_ofExpr(x_637);
x_642 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
x_643 = lean_mk_string_unchecked("", 0, 0);
x_644 = l_Lean_stringToMessageData(x_643);
lean_dec(x_643);
x_645 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_644);
x_646 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_604, x_645, x_7, x_8, x_9, x_10, x_638);
x_647 = lean_ctor_get(x_646, 1);
lean_inc(x_647);
lean_dec(x_646);
x_222 = x_3;
x_223 = x_4;
x_224 = x_5;
x_225 = x_6;
x_226 = x_7;
x_227 = x_8;
x_228 = x_9;
x_229 = x_10;
x_230 = x_647;
goto block_600;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_604);
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
x_648 = lean_ctor_get(x_636, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_636, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_650 = x_636;
} else {
 lean_dec_ref(x_636);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_649);
return x_651;
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_604);
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
x_652 = lean_ctor_get(x_634, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_634, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_654 = x_634;
} else {
 lean_dec_ref(x_634);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 2, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_653);
return x_655;
}
}
}
block_45:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_13);
lean_inc(x_19);
lean_inc(x_16);
lean_inc(x_14);
x_23 = l_Lean_Meta_mkEq(x_17, x_12, x_14, x_16, x_19, x_13, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_mkNot(x_24);
x_27 = l_Lean_Meta_mkDecideProof(x_26, x_14, x_16, x_19, x_13, x_25);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Lean_Expr_app___override(x_29, x_15);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = l_Lean_Expr_app___override(x_32, x_15);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_15);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
block_49:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
block_221:
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_52, sizeof(void*)*13 + 2);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_1);
x_64 = lean_ctor_get_uint8(x_52, sizeof(void*)*13 + 1);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_52, 0);
lean_inc(x_67);
lean_dec(x_52);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_67);
x_68 = l_Lean_Meta_normLitValue(x_67, x_58, x_59, x_60, x_61, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_50);
x_71 = l_Lean_Meta_normLitValue(x_50, x_58, x_59, x_60, x_61, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_expr_eqv(x_69, x_72);
lean_dec(x_72);
lean_dec(x_69);
if (x_74 == 0)
{
x_12 = x_50;
x_13 = x_61;
x_14 = x_58;
x_15 = x_53;
x_16 = x_59;
x_17 = x_67;
x_18 = x_73;
x_19 = x_60;
x_20 = x_64;
goto block_45;
}
else
{
x_12 = x_50;
x_13 = x_61;
x_14 = x_58;
x_15 = x_53;
x_16 = x_59;
x_17 = x_67;
x_18 = x_73;
x_19 = x_60;
x_20 = x_63;
goto block_45;
}
}
else
{
uint8_t x_75; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_50);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_71, 0);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_71);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_50);
x_79 = !lean_is_exclusive(x_68);
if (x_79 == 0)
{
return x_68;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_68, 0);
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_68);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_52, 0);
lean_inc(x_83);
lean_dec(x_52);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_84 = l_Lean_Meta_isConstructorApp_x3f(x_83, x_58, x_59, x_60, x_61, x_62);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_84, 0, x_88);
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_dec(x_84);
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
lean_dec(x_85);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_94 = l_Lean_Meta_isConstructorApp_x3f(x_50, x_58, x_59, x_60, x_61, x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
lean_dec(x_93);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 0);
lean_dec(x_97);
x_98 = lean_box(0);
lean_ctor_set(x_94, 0, x_98);
return x_94;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_dec(x_94);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
lean_dec(x_94);
x_103 = !lean_is_exclusive(x_95);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_95, 0);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_105 = l_Lean_Meta_mkNoConfusion(x_51, x_53, x_58, x_59, x_60, x_61, x_102);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = lean_ctor_get(x_93, 0);
lean_inc(x_109);
lean_dec(x_93);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get(x_104, 0);
lean_inc(x_111);
lean_dec(x_104);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_name_eq(x_110, x_112);
lean_dec(x_112);
lean_dec(x_110);
x_114 = l_instDecidableNot___redArg(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
lean_free_object(x_105);
lean_free_object(x_95);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_107);
x_115 = lean_infer_type(x_107, x_58, x_59, x_60, x_61, x_108);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_118 = l_Lean_Meta_whnfD(x_116, x_58, x_59, x_60, x_61, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 7)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_box(x_63);
x_123 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 14, 3);
lean_closure_set(x_123, 0, x_1);
lean_closure_set(x_123, 1, x_122);
lean_closure_set(x_123, 2, x_107);
x_124 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_121, x_123, x_114, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_120);
return x_124;
}
else
{
uint8_t x_125; 
lean_dec(x_119);
lean_dec(x_107);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_118);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_118, 0);
lean_dec(x_126);
x_127 = lean_box(0);
lean_ctor_set(x_118, 0, x_127);
return x_118;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
lean_dec(x_118);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_107);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_118);
if (x_131 == 0)
{
return x_118;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_118, 0);
x_133 = lean_ctor_get(x_118, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_118);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_107);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_115);
if (x_135 == 0)
{
return x_115;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_115, 0);
x_137 = lean_ctor_get(x_115, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_115);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
lean_ctor_set(x_95, 0, x_107);
lean_ctor_set(x_105, 0, x_95);
return x_105;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_139 = lean_ctor_get(x_105, 0);
x_140 = lean_ctor_get(x_105, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_105);
x_141 = lean_ctor_get(x_93, 0);
lean_inc(x_141);
lean_dec(x_93);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec(x_141);
x_143 = lean_ctor_get(x_104, 0);
lean_inc(x_143);
lean_dec(x_104);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_name_eq(x_142, x_144);
lean_dec(x_144);
lean_dec(x_142);
x_146 = l_instDecidableNot___redArg(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
lean_free_object(x_95);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_139);
x_147 = lean_infer_type(x_139, x_58, x_59, x_60, x_61, x_140);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_150 = l_Lean_Meta_whnfD(x_148, x_58, x_59, x_60, x_61, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 7)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_box(x_63);
x_155 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 14, 3);
lean_closure_set(x_155, 0, x_1);
lean_closure_set(x_155, 1, x_154);
lean_closure_set(x_155, 2, x_139);
x_156 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_153, x_155, x_146, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_152);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_151);
lean_dec(x_139);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_158 = x_150;
} else {
 lean_dec_ref(x_150);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_139);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_161 = lean_ctor_get(x_150, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_150, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_163 = x_150;
} else {
 lean_dec_ref(x_150);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_139);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_165 = lean_ctor_get(x_147, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_147, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_167 = x_147;
} else {
 lean_dec_ref(x_147);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
lean_ctor_set(x_95, 0, x_139);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_95);
lean_ctor_set(x_169, 1, x_140);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_free_object(x_95);
lean_dec(x_104);
lean_dec(x_93);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_105);
if (x_170 == 0)
{
return x_105;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_105, 0);
x_172 = lean_ctor_get(x_105, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_105);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_95, 0);
lean_inc(x_174);
lean_dec(x_95);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
x_175 = l_Lean_Meta_mkNoConfusion(x_51, x_53, x_58, x_59, x_60, x_61, x_102);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_184; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_93, 0);
lean_inc(x_179);
lean_dec(x_93);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_ctor_get(x_174, 0);
lean_inc(x_181);
lean_dec(x_174);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_name_eq(x_180, x_182);
lean_dec(x_182);
lean_dec(x_180);
x_184 = l_instDecidableNot___redArg(x_183);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_178);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_176);
x_185 = lean_infer_type(x_176, x_58, x_59, x_60, x_61, x_177);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
x_188 = l_Lean_Meta_whnfD(x_186, x_58, x_59, x_60, x_61, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 7)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_box(x_63);
x_193 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 14, 3);
lean_closure_set(x_193, 0, x_1);
lean_closure_set(x_193, 1, x_192);
lean_closure_set(x_193, 2, x_176);
x_194 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_191, x_193, x_184, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_190);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_189);
lean_dec(x_176);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
x_197 = lean_box(0);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_195);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_176);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_199 = lean_ctor_get(x_188, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_188, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_201 = x_188;
} else {
 lean_dec_ref(x_188);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_176);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_203 = lean_ctor_get(x_185, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_185, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_205 = x_185;
} else {
 lean_dec_ref(x_185);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_176);
if (lean_is_scalar(x_178)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_178;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_177);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_174);
lean_dec(x_93);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_209 = lean_ctor_get(x_175, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_175, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_211 = x_175;
} else {
 lean_dec_ref(x_175);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_93);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_94);
if (x_213 == 0)
{
return x_94;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_94, 0);
x_215 = lean_ctor_get(x_94, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_94);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_84);
if (x_217 == 0)
{
return x_84;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_84, 0);
x_219 = lean_ctor_get(x_84, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_84);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
block_600:
{
lean_object* x_231; 
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_2);
x_231 = lean_infer_type(x_2, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_231) == 0)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = lean_ctor_get(x_231, 1);
x_235 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_233);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_box(0);
lean_ctor_set(x_231, 0, x_236);
return x_231;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
lean_free_object(x_231);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_242 = lean_st_ref_get(x_222, x_234);
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_242, 0);
x_245 = lean_ctor_get(x_242, 1);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_MVarId_getType(x_246, x_226, x_227, x_228, x_229, x_245);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = l_Lean_Meta_Grind_shareCommon___redArg(x_240, x_225, x_249);
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_250, 0);
x_253 = lean_ctor_get(x_250, 1);
x_254 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_252, x_222, x_253);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_256; 
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_239);
lean_dec(x_222);
lean_dec(x_2);
x_256 = !lean_is_exclusive(x_254);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_257 = lean_ctor_get(x_254, 1);
x_258 = lean_ctor_get(x_254, 0);
lean_dec(x_258);
x_259 = l_Lean_Meta_Grind_getConfig___redArg(x_224, x_257);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get_uint8(x_260, sizeof(void*)*7 + 10);
lean_dec(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
lean_free_object(x_254);
lean_free_object(x_250);
lean_dec(x_252);
lean_free_object(x_242);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_1);
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
lean_dec(x_259);
x_46 = x_262;
goto block_49;
}
else
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_259);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_264 = lean_ctor_get(x_259, 1);
x_265 = lean_ctor_get(x_259, 0);
lean_dec(x_265);
x_266 = lean_mk_string_unchecked("found term that has not been internalized", 41, 41);
x_267 = l_Lean_stringToMessageData(x_266);
lean_dec(x_266);
x_268 = l_Lean_indentExpr(x_252);
lean_ctor_set_tag(x_259, 7);
lean_ctor_set(x_259, 1, x_268);
lean_ctor_set(x_259, 0, x_267);
x_269 = lean_mk_string_unchecked("\nwhile trying to construct a proof for `MatchCond`", 50, 50);
x_270 = l_Lean_stringToMessageData(x_269);
lean_dec(x_269);
lean_ctor_set_tag(x_254, 7);
lean_ctor_set(x_254, 1, x_270);
lean_ctor_set(x_254, 0, x_259);
x_271 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_250, 7);
lean_ctor_set(x_250, 1, x_271);
lean_ctor_set(x_250, 0, x_254);
x_272 = lean_mk_string_unchecked("", 0, 0);
x_273 = l_Lean_stringToMessageData(x_272);
lean_dec(x_272);
lean_ctor_set_tag(x_242, 7);
lean_ctor_set(x_242, 1, x_273);
lean_ctor_set(x_242, 0, x_250);
x_274 = l_Lean_Meta_Grind_reportIssue(x_242, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_264);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_46 = x_275;
goto block_49;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_276 = lean_ctor_get(x_259, 1);
lean_inc(x_276);
lean_dec(x_259);
x_277 = lean_mk_string_unchecked("found term that has not been internalized", 41, 41);
x_278 = l_Lean_stringToMessageData(x_277);
lean_dec(x_277);
x_279 = l_Lean_indentExpr(x_252);
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_mk_string_unchecked("\nwhile trying to construct a proof for `MatchCond`", 50, 50);
x_282 = l_Lean_stringToMessageData(x_281);
lean_dec(x_281);
lean_ctor_set_tag(x_254, 7);
lean_ctor_set(x_254, 1, x_282);
lean_ctor_set(x_254, 0, x_280);
x_283 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_250, 7);
lean_ctor_set(x_250, 1, x_283);
lean_ctor_set(x_250, 0, x_254);
x_284 = lean_mk_string_unchecked("", 0, 0);
x_285 = l_Lean_stringToMessageData(x_284);
lean_dec(x_284);
lean_ctor_set_tag(x_242, 7);
lean_ctor_set(x_242, 1, x_285);
lean_ctor_set(x_242, 0, x_250);
x_286 = l_Lean_Meta_Grind_reportIssue(x_242, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_276);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
x_46 = x_287;
goto block_49;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_288 = lean_ctor_get(x_254, 1);
lean_inc(x_288);
lean_dec(x_254);
x_289 = l_Lean_Meta_Grind_getConfig___redArg(x_224, x_288);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get_uint8(x_290, sizeof(void*)*7 + 10);
lean_dec(x_290);
if (x_291 == 0)
{
lean_object* x_292; 
lean_free_object(x_250);
lean_dec(x_252);
lean_free_object(x_242);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_1);
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_292);
lean_dec(x_289);
x_46 = x_292;
goto block_49;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_293 = lean_ctor_get(x_289, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_294 = x_289;
} else {
 lean_dec_ref(x_289);
 x_294 = lean_box(0);
}
x_295 = lean_mk_string_unchecked("found term that has not been internalized", 41, 41);
x_296 = l_Lean_stringToMessageData(x_295);
lean_dec(x_295);
x_297 = l_Lean_indentExpr(x_252);
if (lean_is_scalar(x_294)) {
 x_298 = lean_alloc_ctor(7, 2, 0);
} else {
 x_298 = x_294;
 lean_ctor_set_tag(x_298, 7);
}
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_mk_string_unchecked("\nwhile trying to construct a proof for `MatchCond`", 50, 50);
x_300 = l_Lean_stringToMessageData(x_299);
lean_dec(x_299);
x_301 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_250, 7);
lean_ctor_set(x_250, 1, x_302);
lean_ctor_set(x_250, 0, x_301);
x_303 = lean_mk_string_unchecked("", 0, 0);
x_304 = l_Lean_stringToMessageData(x_303);
lean_dec(x_303);
lean_ctor_set_tag(x_242, 7);
lean_ctor_set(x_242, 1, x_304);
lean_ctor_set(x_242, 0, x_250);
x_305 = l_Lean_Meta_Grind_reportIssue(x_242, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_293);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_46 = x_306;
goto block_49;
}
}
}
else
{
lean_free_object(x_250);
lean_free_object(x_242);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_307 = lean_ctor_get(x_254, 1);
lean_inc(x_307);
lean_dec(x_254);
x_308 = lean_ctor_get(x_255, 0);
lean_inc(x_308);
lean_dec(x_255);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
x_310 = lean_grind_mk_eq_proof(x_309, x_252, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_307);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_313 = l_Lean_Meta_mkEqTrans(x_311, x_2, x_226, x_227, x_228, x_229, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_50 = x_241;
x_51 = x_248;
x_52 = x_308;
x_53 = x_314;
x_54 = x_222;
x_55 = x_223;
x_56 = x_224;
x_57 = x_225;
x_58 = x_226;
x_59 = x_227;
x_60 = x_228;
x_61 = x_229;
x_62 = x_315;
goto block_221;
}
else
{
uint8_t x_316; 
lean_dec(x_308);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_316 = !lean_is_exclusive(x_313);
if (x_316 == 0)
{
return x_313;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_313, 0);
x_318 = lean_ctor_get(x_313, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_313);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
else
{
uint8_t x_320; 
lean_dec(x_308);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_310);
if (x_320 == 0)
{
return x_310;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_310, 0);
x_322 = lean_ctor_get(x_310, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_310);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_239);
x_324 = lean_ctor_get(x_254, 1);
lean_inc(x_324);
lean_dec(x_254);
x_325 = lean_ctor_get(x_255, 0);
lean_inc(x_325);
lean_dec(x_255);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
x_327 = lean_grind_mk_heq_proof(x_326, x_252, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_324);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_330 = l_Lean_Meta_mkHEqTrans(x_328, x_2, x_226, x_227, x_228, x_229, x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_box(0);
x_334 = lean_unbox(x_333);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_335 = l_Lean_Meta_mkEqOfHEq(x_331, x_334, x_226, x_227, x_228, x_229, x_332);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_50 = x_241;
x_51 = x_248;
x_52 = x_325;
x_53 = x_336;
x_54 = x_222;
x_55 = x_223;
x_56 = x_224;
x_57 = x_225;
x_58 = x_226;
x_59 = x_227;
x_60 = x_228;
x_61 = x_229;
x_62 = x_337;
goto block_221;
}
else
{
uint8_t x_338; 
lean_dec(x_325);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_338 = !lean_is_exclusive(x_335);
if (x_338 == 0)
{
return x_335;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_335, 0);
x_340 = lean_ctor_get(x_335, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_335);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
else
{
uint8_t x_342; 
lean_dec(x_325);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_342 = !lean_is_exclusive(x_330);
if (x_342 == 0)
{
return x_330;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_330, 0);
x_344 = lean_ctor_get(x_330, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_330);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
else
{
uint8_t x_346; 
lean_dec(x_325);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_346 = !lean_is_exclusive(x_327);
if (x_346 == 0)
{
return x_327;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_327, 0);
x_348 = lean_ctor_get(x_327, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_327);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_250, 0);
x_351 = lean_ctor_get(x_250, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_250);
x_352 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_350, x_222, x_351);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_239);
lean_dec(x_222);
lean_dec(x_2);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_355 = x_352;
} else {
 lean_dec_ref(x_352);
 x_355 = lean_box(0);
}
x_356 = l_Lean_Meta_Grind_getConfig___redArg(x_224, x_354);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get_uint8(x_357, sizeof(void*)*7 + 10);
lean_dec(x_357);
if (x_358 == 0)
{
lean_object* x_359; 
lean_dec(x_355);
lean_dec(x_350);
lean_free_object(x_242);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_1);
x_359 = lean_ctor_get(x_356, 1);
lean_inc(x_359);
lean_dec(x_356);
x_46 = x_359;
goto block_49;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_360 = lean_ctor_get(x_356, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_361 = x_356;
} else {
 lean_dec_ref(x_356);
 x_361 = lean_box(0);
}
x_362 = lean_mk_string_unchecked("found term that has not been internalized", 41, 41);
x_363 = l_Lean_stringToMessageData(x_362);
lean_dec(x_362);
x_364 = l_Lean_indentExpr(x_350);
if (lean_is_scalar(x_361)) {
 x_365 = lean_alloc_ctor(7, 2, 0);
} else {
 x_365 = x_361;
 lean_ctor_set_tag(x_365, 7);
}
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_mk_string_unchecked("\nwhile trying to construct a proof for `MatchCond`", 50, 50);
x_367 = l_Lean_stringToMessageData(x_366);
lean_dec(x_366);
if (lean_is_scalar(x_355)) {
 x_368 = lean_alloc_ctor(7, 2, 0);
} else {
 x_368 = x_355;
 lean_ctor_set_tag(x_368, 7);
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_367);
x_369 = l_Lean_indentExpr(x_1);
x_370 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = lean_mk_string_unchecked("", 0, 0);
x_372 = l_Lean_stringToMessageData(x_371);
lean_dec(x_371);
lean_ctor_set_tag(x_242, 7);
lean_ctor_set(x_242, 1, x_372);
lean_ctor_set(x_242, 0, x_370);
x_373 = l_Lean_Meta_Grind_reportIssue(x_242, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_360);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
lean_dec(x_373);
x_46 = x_374;
goto block_49;
}
}
else
{
lean_free_object(x_242);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = lean_ctor_get(x_352, 1);
lean_inc(x_375);
lean_dec(x_352);
x_376 = lean_ctor_get(x_353, 0);
lean_inc(x_376);
lean_dec(x_353);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
x_378 = lean_grind_mk_eq_proof(x_377, x_350, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_375);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_381 = l_Lean_Meta_mkEqTrans(x_379, x_2, x_226, x_227, x_228, x_229, x_380);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_50 = x_241;
x_51 = x_248;
x_52 = x_376;
x_53 = x_382;
x_54 = x_222;
x_55 = x_223;
x_56 = x_224;
x_57 = x_225;
x_58 = x_226;
x_59 = x_227;
x_60 = x_228;
x_61 = x_229;
x_62 = x_383;
goto block_221;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_376);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_384 = lean_ctor_get(x_381, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_381, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_386 = x_381;
} else {
 lean_dec_ref(x_381);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_385);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_376);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_388 = lean_ctor_get(x_378, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_378, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_390 = x_378;
} else {
 lean_dec_ref(x_378);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_239);
x_392 = lean_ctor_get(x_352, 1);
lean_inc(x_392);
lean_dec(x_352);
x_393 = lean_ctor_get(x_353, 0);
lean_inc(x_393);
lean_dec(x_353);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
x_395 = lean_grind_mk_heq_proof(x_394, x_350, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_392);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_398 = l_Lean_Meta_mkHEqTrans(x_396, x_2, x_226, x_227, x_228, x_229, x_397);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_box(0);
x_402 = lean_unbox(x_401);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_403 = l_Lean_Meta_mkEqOfHEq(x_399, x_402, x_226, x_227, x_228, x_229, x_400);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_50 = x_241;
x_51 = x_248;
x_52 = x_393;
x_53 = x_404;
x_54 = x_222;
x_55 = x_223;
x_56 = x_224;
x_57 = x_225;
x_58 = x_226;
x_59 = x_227;
x_60 = x_228;
x_61 = x_229;
x_62 = x_405;
goto block_221;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_393);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
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
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_393);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_410 = lean_ctor_get(x_398, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_398, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_412 = x_398;
} else {
 lean_dec_ref(x_398);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_393);
lean_dec(x_248);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_414 = lean_ctor_get(x_395, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_395, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_416 = x_395;
} else {
 lean_dec_ref(x_395);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
}
}
}
else
{
uint8_t x_418; 
lean_free_object(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_418 = !lean_is_exclusive(x_247);
if (x_418 == 0)
{
return x_247;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_247, 0);
x_420 = lean_ctor_get(x_247, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_247);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_242, 0);
x_423 = lean_ctor_get(x_242, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_242);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
lean_dec(x_422);
x_425 = l_Lean_MVarId_getType(x_424, x_226, x_227, x_228, x_229, x_423);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = l_Lean_Meta_Grind_shareCommon___redArg(x_240, x_225, x_427);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_431 = x_428;
} else {
 lean_dec_ref(x_428);
 x_431 = lean_box(0);
}
x_432 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_429, x_222, x_430);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; 
lean_dec(x_426);
lean_dec(x_241);
lean_dec(x_239);
lean_dec(x_222);
lean_dec(x_2);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_435 = x_432;
} else {
 lean_dec_ref(x_432);
 x_435 = lean_box(0);
}
x_436 = l_Lean_Meta_Grind_getConfig___redArg(x_224, x_434);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get_uint8(x_437, sizeof(void*)*7 + 10);
lean_dec(x_437);
if (x_438 == 0)
{
lean_object* x_439; 
lean_dec(x_435);
lean_dec(x_431);
lean_dec(x_429);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_1);
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_dec(x_436);
x_46 = x_439;
goto block_49;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_440 = lean_ctor_get(x_436, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_441 = x_436;
} else {
 lean_dec_ref(x_436);
 x_441 = lean_box(0);
}
x_442 = lean_mk_string_unchecked("found term that has not been internalized", 41, 41);
x_443 = l_Lean_stringToMessageData(x_442);
lean_dec(x_442);
x_444 = l_Lean_indentExpr(x_429);
if (lean_is_scalar(x_441)) {
 x_445 = lean_alloc_ctor(7, 2, 0);
} else {
 x_445 = x_441;
 lean_ctor_set_tag(x_445, 7);
}
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_mk_string_unchecked("\nwhile trying to construct a proof for `MatchCond`", 50, 50);
x_447 = l_Lean_stringToMessageData(x_446);
lean_dec(x_446);
if (lean_is_scalar(x_435)) {
 x_448 = lean_alloc_ctor(7, 2, 0);
} else {
 x_448 = x_435;
 lean_ctor_set_tag(x_448, 7);
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_447);
x_449 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_431)) {
 x_450 = lean_alloc_ctor(7, 2, 0);
} else {
 x_450 = x_431;
 lean_ctor_set_tag(x_450, 7);
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_mk_string_unchecked("", 0, 0);
x_452 = l_Lean_stringToMessageData(x_451);
lean_dec(x_451);
x_453 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_452);
x_454 = l_Lean_Meta_Grind_reportIssue(x_453, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_440);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
x_455 = lean_ctor_get(x_454, 1);
lean_inc(x_455);
lean_dec(x_454);
x_46 = x_455;
goto block_49;
}
}
else
{
lean_dec(x_431);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_456 = lean_ctor_get(x_432, 1);
lean_inc(x_456);
lean_dec(x_432);
x_457 = lean_ctor_get(x_433, 0);
lean_inc(x_457);
lean_dec(x_433);
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
x_459 = lean_grind_mk_eq_proof(x_458, x_429, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_456);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_462 = l_Lean_Meta_mkEqTrans(x_460, x_2, x_226, x_227, x_228, x_229, x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_50 = x_241;
x_51 = x_426;
x_52 = x_457;
x_53 = x_463;
x_54 = x_222;
x_55 = x_223;
x_56 = x_224;
x_57 = x_225;
x_58 = x_226;
x_59 = x_227;
x_60 = x_228;
x_61 = x_229;
x_62 = x_464;
goto block_221;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_457);
lean_dec(x_426);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_465 = lean_ctor_get(x_462, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_462, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_467 = x_462;
} else {
 lean_dec_ref(x_462);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_466);
return x_468;
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_457);
lean_dec(x_426);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_469 = lean_ctor_get(x_459, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_471 = x_459;
} else {
 lean_dec_ref(x_459);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
return x_472;
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_239);
x_473 = lean_ctor_get(x_432, 1);
lean_inc(x_473);
lean_dec(x_432);
x_474 = lean_ctor_get(x_433, 0);
lean_inc(x_474);
lean_dec(x_433);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
x_476 = lean_grind_mk_heq_proof(x_475, x_429, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_473);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_479 = l_Lean_Meta_mkHEqTrans(x_477, x_2, x_226, x_227, x_228, x_229, x_478);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
x_482 = lean_box(0);
x_483 = lean_unbox(x_482);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_484 = l_Lean_Meta_mkEqOfHEq(x_480, x_483, x_226, x_227, x_228, x_229, x_481);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
x_50 = x_241;
x_51 = x_426;
x_52 = x_474;
x_53 = x_485;
x_54 = x_222;
x_55 = x_223;
x_56 = x_224;
x_57 = x_225;
x_58 = x_226;
x_59 = x_227;
x_60 = x_228;
x_61 = x_229;
x_62 = x_486;
goto block_221;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_474);
lean_dec(x_426);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_487 = lean_ctor_get(x_484, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_484, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_489 = x_484;
} else {
 lean_dec_ref(x_484);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_474);
lean_dec(x_426);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_491 = lean_ctor_get(x_479, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_479, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_493 = x_479;
} else {
 lean_dec_ref(x_479);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_492);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_474);
lean_dec(x_426);
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_495 = lean_ctor_get(x_476, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_476, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_497 = x_476;
} else {
 lean_dec_ref(x_476);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
}
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_499 = lean_ctor_get(x_425, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_425, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_501 = x_425;
} else {
 lean_dec_ref(x_425);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_500);
return x_502;
}
}
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_231, 0);
x_504 = lean_ctor_get(x_231, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_231);
x_505 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_503);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_506 = lean_box(0);
x_507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_504);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_508 = lean_ctor_get(x_505, 0);
lean_inc(x_508);
lean_dec(x_505);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_ctor_get(x_509, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_509, 1);
lean_inc(x_512);
lean_dec(x_509);
x_513 = lean_st_ref_get(x_222, x_504);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_516 = x_513;
} else {
 lean_dec_ref(x_513);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_514, 0);
lean_inc(x_517);
lean_dec(x_514);
x_518 = l_Lean_MVarId_getType(x_517, x_226, x_227, x_228, x_229, x_515);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = l_Lean_Meta_Grind_shareCommon___redArg(x_511, x_225, x_520);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_524 = x_521;
} else {
 lean_dec_ref(x_521);
 x_524 = lean_box(0);
}
x_525 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_522, x_222, x_523);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; 
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_510);
lean_dec(x_222);
lean_dec(x_2);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_528 = x_525;
} else {
 lean_dec_ref(x_525);
 x_528 = lean_box(0);
}
x_529 = l_Lean_Meta_Grind_getConfig___redArg(x_224, x_527);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get_uint8(x_530, sizeof(void*)*7 + 10);
lean_dec(x_530);
if (x_531 == 0)
{
lean_object* x_532; 
lean_dec(x_528);
lean_dec(x_524);
lean_dec(x_522);
lean_dec(x_516);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_1);
x_532 = lean_ctor_get(x_529, 1);
lean_inc(x_532);
lean_dec(x_529);
x_46 = x_532;
goto block_49;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_533 = lean_ctor_get(x_529, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_534 = x_529;
} else {
 lean_dec_ref(x_529);
 x_534 = lean_box(0);
}
x_535 = lean_mk_string_unchecked("found term that has not been internalized", 41, 41);
x_536 = l_Lean_stringToMessageData(x_535);
lean_dec(x_535);
x_537 = l_Lean_indentExpr(x_522);
if (lean_is_scalar(x_534)) {
 x_538 = lean_alloc_ctor(7, 2, 0);
} else {
 x_538 = x_534;
 lean_ctor_set_tag(x_538, 7);
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
x_539 = lean_mk_string_unchecked("\nwhile trying to construct a proof for `MatchCond`", 50, 50);
x_540 = l_Lean_stringToMessageData(x_539);
lean_dec(x_539);
if (lean_is_scalar(x_528)) {
 x_541 = lean_alloc_ctor(7, 2, 0);
} else {
 x_541 = x_528;
 lean_ctor_set_tag(x_541, 7);
}
lean_ctor_set(x_541, 0, x_538);
lean_ctor_set(x_541, 1, x_540);
x_542 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_524)) {
 x_543 = lean_alloc_ctor(7, 2, 0);
} else {
 x_543 = x_524;
 lean_ctor_set_tag(x_543, 7);
}
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
x_544 = lean_mk_string_unchecked("", 0, 0);
x_545 = l_Lean_stringToMessageData(x_544);
lean_dec(x_544);
if (lean_is_scalar(x_516)) {
 x_546 = lean_alloc_ctor(7, 2, 0);
} else {
 x_546 = x_516;
 lean_ctor_set_tag(x_546, 7);
}
lean_ctor_set(x_546, 0, x_543);
lean_ctor_set(x_546, 1, x_545);
x_547 = l_Lean_Meta_Grind_reportIssue(x_546, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_533);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
lean_dec(x_547);
x_46 = x_548;
goto block_49;
}
}
else
{
lean_dec(x_524);
lean_dec(x_516);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_549 = lean_ctor_get(x_525, 1);
lean_inc(x_549);
lean_dec(x_525);
x_550 = lean_ctor_get(x_526, 0);
lean_inc(x_550);
lean_dec(x_526);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
x_552 = lean_grind_mk_eq_proof(x_551, x_522, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_549);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_555 = l_Lean_Meta_mkEqTrans(x_553, x_2, x_226, x_227, x_228, x_229, x_554);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_50 = x_512;
x_51 = x_519;
x_52 = x_550;
x_53 = x_556;
x_54 = x_222;
x_55 = x_223;
x_56 = x_224;
x_57 = x_225;
x_58 = x_226;
x_59 = x_227;
x_60 = x_228;
x_61 = x_229;
x_62 = x_557;
goto block_221;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_550);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_558 = lean_ctor_get(x_555, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_555, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_560 = x_555;
} else {
 lean_dec_ref(x_555);
 x_560 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_561 = x_560;
}
lean_ctor_set(x_561, 0, x_558);
lean_ctor_set(x_561, 1, x_559);
return x_561;
}
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_550);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_562 = lean_ctor_get(x_552, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_552, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_564 = x_552;
} else {
 lean_dec_ref(x_552);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(1, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_563);
return x_565;
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_510);
x_566 = lean_ctor_get(x_525, 1);
lean_inc(x_566);
lean_dec(x_525);
x_567 = lean_ctor_get(x_526, 0);
lean_inc(x_567);
lean_dec(x_526);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
x_569 = lean_grind_mk_heq_proof(x_568, x_522, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_566);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_572 = l_Lean_Meta_mkHEqTrans(x_570, x_2, x_226, x_227, x_228, x_229, x_571);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
x_575 = lean_box(0);
x_576 = lean_unbox(x_575);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
x_577 = l_Lean_Meta_mkEqOfHEq(x_573, x_576, x_226, x_227, x_228, x_229, x_574);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
x_50 = x_512;
x_51 = x_519;
x_52 = x_567;
x_53 = x_578;
x_54 = x_222;
x_55 = x_223;
x_56 = x_224;
x_57 = x_225;
x_58 = x_226;
x_59 = x_227;
x_60 = x_228;
x_61 = x_229;
x_62 = x_579;
goto block_221;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_567);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_580 = lean_ctor_get(x_577, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_577, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_582 = x_577;
} else {
 lean_dec_ref(x_577);
 x_582 = lean_box(0);
}
if (lean_is_scalar(x_582)) {
 x_583 = lean_alloc_ctor(1, 2, 0);
} else {
 x_583 = x_582;
}
lean_ctor_set(x_583, 0, x_580);
lean_ctor_set(x_583, 1, x_581);
return x_583;
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_567);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_1);
x_584 = lean_ctor_get(x_572, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_572, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_586 = x_572;
} else {
 lean_dec_ref(x_572);
 x_586 = lean_box(0);
}
if (lean_is_scalar(x_586)) {
 x_587 = lean_alloc_ctor(1, 2, 0);
} else {
 x_587 = x_586;
}
lean_ctor_set(x_587, 0, x_584);
lean_ctor_set(x_587, 1, x_585);
return x_587;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_567);
lean_dec(x_519);
lean_dec(x_512);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_588 = lean_ctor_get(x_569, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_569, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_590 = x_569;
} else {
 lean_dec_ref(x_569);
 x_590 = lean_box(0);
}
if (lean_is_scalar(x_590)) {
 x_591 = lean_alloc_ctor(1, 2, 0);
} else {
 x_591 = x_590;
}
lean_ctor_set(x_591, 0, x_588);
lean_ctor_set(x_591, 1, x_589);
return x_591;
}
}
}
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_516);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_592 = lean_ctor_get(x_518, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_518, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_594 = x_518;
} else {
 lean_dec_ref(x_518);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
return x_595;
}
}
}
}
else
{
uint8_t x_596; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_2);
lean_dec(x_1);
x_596 = !lean_is_exclusive(x_231);
if (x_596 == 0)
{
return x_231;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_231, 0);
x_598 = lean_ctor_get(x_231, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_231);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args) {
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
uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_21 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(x_1, x_2, x_18, x_4, x_5, x_19, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_5);
lean_dec(x_2);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_6, x_5);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_26 = lean_array_uget(x_4, x_6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_26);
x_27 = lean_infer_type(x_26, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_28);
x_30 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_93; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_93 = lean_unbox(x_31);
lean_dec(x_31);
if (x_93 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
x_17 = x_35;
x_18 = x_32;
goto block_23;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_94 = lean_mk_string_unchecked("grind", 5, 5);
x_95 = lean_mk_string_unchecked("debug", 5, 5);
x_96 = lean_mk_string_unchecked("matchCond", 9, 9);
x_97 = l_Lean_Name_mkStr3(x_94, x_95, x_96);
lean_inc(x_97);
x_98 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_97, x_14, x_32);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_97);
lean_dec(x_28);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_15;
x_44 = x_101;
goto block_92;
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_98);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_98, 1);
x_104 = lean_ctor_get(x_98, 0);
lean_dec(x_104);
x_105 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked(">>> ", 4, 4);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = l_Lean_MessageData_ofExpr(x_28);
lean_ctor_set_tag(x_98, 7);
lean_ctor_set(x_98, 1, x_109);
lean_ctor_set(x_98, 0, x_108);
x_110 = lean_mk_string_unchecked("", 0, 0);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_98);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_97, x_112, x_12, x_13, x_14, x_15, x_106);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_15;
x_44 = x_114;
goto block_92;
}
else
{
uint8_t x_115; 
lean_free_object(x_98);
lean_dec(x_97);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_105);
if (x_115 == 0)
{
return x_105;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_105, 0);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_105);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
lean_dec(x_98);
x_120 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_mk_string_unchecked(">>> ", 4, 4);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
x_124 = l_Lean_MessageData_ofExpr(x_28);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked("", 0, 0);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_97, x_128, x_12, x_13, x_14, x_15, x_121);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_15;
x_44 = x_130;
goto block_92;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_97);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_131 = lean_ctor_get(x_120, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_120, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_133 = x_120;
} else {
 lean_dec_ref(x_120);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
block_92:
{
lean_object* x_45; 
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_1);
x_45 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(x_1, x_26, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_17 = x_35;
x_18 = x_47;
goto block_23;
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_box(0);
x_52 = lean_box(1);
x_53 = lean_unbox(x_51);
x_54 = lean_unbox(x_51);
x_55 = lean_unbox(x_52);
x_56 = l_Lean_Meta_mkLambdaFVars(x_2, x_50, x_53, x_3, x_54, x_55, x_40, x_41, x_42, x_43, x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
lean_ctor_set(x_46, 0, x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_46);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_34);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_56, 0);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_56);
lean_ctor_set(x_46, 0, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_46);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_34);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_free_object(x_46);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
return x_56;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
lean_dec(x_46);
x_71 = lean_box(0);
x_72 = lean_box(1);
x_73 = lean_unbox(x_71);
x_74 = lean_unbox(x_71);
x_75 = lean_unbox(x_72);
x_76 = l_Lean_Meta_mkLambdaFVars(x_2, x_70, x_73, x_3, x_74, x_75, x_40, x_41, x_42, x_43, x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_34);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_86 = x_76;
} else {
 lean_dec_ref(x_76);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_45);
if (x_88 == 0)
{
return x_45;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_45, 0);
x_90 = lean_ctor_get(x_45, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_45);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_30);
if (x_135 == 0)
{
return x_30;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_30, 0);
x_137 = lean_ctor_get(x_30, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_30);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_27);
if (x_139 == 0)
{
return x_27;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_27, 0);
x_141 = lean_ctor_get(x_27, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_27);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_6, x_20);
x_6 = x_21;
x_7 = x_17;
x_16 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_6, x_5);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_26 = lean_array_uget(x_4, x_6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_26);
x_27 = lean_infer_type(x_26, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_28);
x_30 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_93; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_93 = lean_unbox(x_31);
lean_dec(x_31);
if (x_93 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
x_17 = x_35;
x_18 = x_32;
goto block_23;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_94 = lean_mk_string_unchecked("grind", 5, 5);
x_95 = lean_mk_string_unchecked("debug", 5, 5);
x_96 = lean_mk_string_unchecked("matchCond", 9, 9);
x_97 = l_Lean_Name_mkStr3(x_94, x_95, x_96);
lean_inc(x_97);
x_98 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_97, x_14, x_32);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_97);
lean_dec(x_28);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_15;
x_44 = x_101;
goto block_92;
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_98);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_98, 1);
x_104 = lean_ctor_get(x_98, 0);
lean_dec(x_104);
x_105 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked(">>> ", 4, 4);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = l_Lean_MessageData_ofExpr(x_28);
lean_ctor_set_tag(x_98, 7);
lean_ctor_set(x_98, 1, x_109);
lean_ctor_set(x_98, 0, x_108);
x_110 = lean_mk_string_unchecked("", 0, 0);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_98);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_97, x_112, x_12, x_13, x_14, x_15, x_106);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_15;
x_44 = x_114;
goto block_92;
}
else
{
uint8_t x_115; 
lean_free_object(x_98);
lean_dec(x_97);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_105);
if (x_115 == 0)
{
return x_105;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_105, 0);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_105);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
lean_dec(x_98);
x_120 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_mk_string_unchecked(">>> ", 4, 4);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
x_124 = l_Lean_MessageData_ofExpr(x_28);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked("", 0, 0);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_97, x_128, x_12, x_13, x_14, x_15, x_121);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_15;
x_44 = x_130;
goto block_92;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_97);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_131 = lean_ctor_get(x_120, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_120, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_133 = x_120;
} else {
 lean_dec_ref(x_120);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
block_92:
{
lean_object* x_45; 
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_1);
x_45 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(x_1, x_26, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_17 = x_35;
x_18 = x_47;
goto block_23;
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_box(0);
x_52 = lean_box(1);
x_53 = lean_unbox(x_51);
x_54 = lean_unbox(x_51);
x_55 = lean_unbox(x_52);
x_56 = l_Lean_Meta_mkLambdaFVars(x_2, x_50, x_53, x_3, x_54, x_55, x_40, x_41, x_42, x_43, x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
lean_ctor_set(x_46, 0, x_58);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_46);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_34);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_56, 0);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_56);
lean_ctor_set(x_46, 0, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_46);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_34);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_free_object(x_46);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
return x_56;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
lean_dec(x_46);
x_71 = lean_box(0);
x_72 = lean_box(1);
x_73 = lean_unbox(x_71);
x_74 = lean_unbox(x_71);
x_75 = lean_unbox(x_72);
x_76 = l_Lean_Meta_mkLambdaFVars(x_2, x_70, x_73, x_3, x_74, x_75, x_40, x_41, x_42, x_43, x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_34);
if (lean_is_scalar(x_79)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_79;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_86 = x_76;
} else {
 lean_dec_ref(x_76);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_45);
if (x_88 == 0)
{
return x_45;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_45, 0);
x_90 = lean_ctor_get(x_45, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_45);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_30);
if (x_135 == 0)
{
return x_30;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_30, 0);
x_137 = lean_ctor_get(x_30, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_30);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_27);
if (x_139 == 0)
{
return x_27;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_27, 0);
x_141 = lean_ctor_get(x_27, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_27);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_6, x_20);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_21, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_size(x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(x_1, x_3, x_2, x_3, x_17, x_19, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_31);
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_18 = l_Lean_Expr_cleanupAnnotations(x_12);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_inc(x_18);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("Grind", 5, 5);
x_23 = lean_mk_string_unchecked("MatchCond", 9, 9);
x_24 = l_Lean_Name_mkStr3(x_21, x_22, x_23);
x_25 = l_Lean_Expr_isConstOf(x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
if (x_25 == 0)
{
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_14);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_box(x_25);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 13, 2);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_26, x_28, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_31;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0(x_1, x_2, x_17, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(x_1, x_2, x_17, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_nat_dec_lt(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_array_get(x_18, x_17, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_19);
x_20 = l_Lean_Meta_Grind_tryToProveFalse_go(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_28; size_t x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_28 = lean_ptr_addr(x_19);
lean_dec(x_19);
x_29 = lean_ptr_addr(x_21);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_31 = lean_array_set(x_17, x_4, x_21);
x_32 = lean_box(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_23 = x_33;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
x_23 = x_35;
goto block_27;
}
block_27:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_3 = x_23;
x_4 = x_25;
x_13 = x_22;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_Grind_getRootENode___redArg(x_1, x_2, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*13 + 2);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*13 + 1);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_26);
x_27 = l_Lean_Meta_isConstructorApp_x3f(x_26, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = l_Lean_Expr_sort___override(x_35);
x_37 = l_Lean_Expr_getAppNumArgs(x_26);
lean_inc(x_37);
x_38 = lean_mk_array(x_37, x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_37, x_39);
lean_dec(x_37);
lean_inc(x_26);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_26, x_38, x_40);
x_42 = lean_box(0);
x_43 = lean_ctor_get(x_34, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 4);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_nat_add(x_43, x_44);
lean_dec(x_44);
lean_inc(x_43);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
x_48 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(x_13, x_46, x_47, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
lean_ctor_set(x_48, 0, x_26);
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_dec(x_48);
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_dec(x_49);
x_58 = l_Lean_Expr_getAppFn(x_26);
lean_dec(x_26);
x_59 = l_Lean_mkAppN(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_Meta_Grind_shareCommon___redArg(x_59, x_5, x_56);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_26);
x_61 = !lean_is_exclusive(x_48);
if (x_61 == 0)
{
return x_48;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_48, 0);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_48);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_27);
if (x_65 == 0)
{
return x_27;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_27, 0);
x_67 = lean_ctor_get(x_27, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_27);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
return x_11;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_11, 0);
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_11);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_tryToProveFalse_go_spec__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_tryToProveFalse_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_3, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_array_fget(x_30, x_25);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_25, x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_26);
if (x_32 == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
x_14 = x_36;
x_15 = x_13;
goto block_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_83; 
x_37 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_37);
x_83 = lean_infer_type(x_37, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
x_87 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_35);
lean_ctor_set(x_83, 0, x_90);
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_free_object(x_83);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_91, 1);
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_96);
x_99 = l_Lean_Meta_Grind_tryToProveFalse_go(x_96, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_86);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_184 = lean_mk_string_unchecked("grind", 5, 5);
x_185 = lean_mk_string_unchecked("debug", 5, 5);
x_186 = lean_mk_string_unchecked("matchCond", 9, 9);
x_187 = lean_mk_string_unchecked("proveFalse", 10, 10);
x_188 = l_Lean_Name_mkStr4(x_184, x_185, x_186, x_187);
lean_inc(x_188);
x_189 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_188, x_11, x_101);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
lean_dec(x_188);
lean_free_object(x_91);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_192;
goto block_183;
}
else
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_189);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_194 = lean_ctor_get(x_189, 1);
x_195 = lean_ctor_get(x_189, 0);
lean_dec(x_195);
x_196 = lean_mk_string_unchecked("", 0, 0);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
lean_inc(x_100);
x_198 = l_Lean_MessageData_ofExpr(x_100);
lean_inc(x_197);
lean_ctor_set_tag(x_189, 7);
lean_ctor_set(x_189, 1, x_198);
lean_ctor_set(x_189, 0, x_197);
x_199 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_200 = l_Lean_stringToMessageData(x_199);
lean_dec(x_199);
lean_ctor_set_tag(x_91, 7);
lean_ctor_set(x_91, 1, x_200);
lean_ctor_set(x_91, 0, x_189);
lean_inc(x_97);
x_201 = l_Lean_MessageData_ofExpr(x_97);
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_91);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_197);
x_204 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_188, x_203, x_9, x_10, x_11, x_12, x_194);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_205;
goto block_183;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_206 = lean_ctor_get(x_189, 1);
lean_inc(x_206);
lean_dec(x_189);
x_207 = lean_mk_string_unchecked("", 0, 0);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
lean_inc(x_100);
x_209 = l_Lean_MessageData_ofExpr(x_100);
lean_inc(x_208);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
lean_ctor_set_tag(x_91, 7);
lean_ctor_set(x_91, 1, x_212);
lean_ctor_set(x_91, 0, x_210);
lean_inc(x_97);
x_213 = l_Lean_MessageData_ofExpr(x_97);
x_214 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_214, 0, x_91);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_208);
x_216 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_188, x_215, x_9, x_10, x_11, x_12, x_206);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_217;
goto block_183;
}
}
block_183:
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; uint64_t x_132; lean_object* x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint8_t x_137; uint64_t x_138; uint64_t x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
x_111 = lean_box(1);
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
x_113 = lean_ctor_get_uint8(x_112, 0);
x_114 = lean_ctor_get_uint8(x_112, 1);
x_115 = lean_ctor_get_uint8(x_112, 2);
x_116 = lean_ctor_get_uint8(x_112, 3);
x_117 = lean_ctor_get_uint8(x_112, 4);
x_118 = lean_ctor_get_uint8(x_112, 5);
x_119 = lean_ctor_get_uint8(x_112, 6);
x_120 = lean_ctor_get_uint8(x_112, 7);
x_121 = lean_ctor_get_uint8(x_112, 8);
x_122 = lean_ctor_get_uint8(x_112, 10);
x_123 = lean_ctor_get_uint8(x_112, 11);
x_124 = lean_ctor_get_uint8(x_112, 12);
x_125 = lean_ctor_get_uint8(x_112, 13);
x_126 = lean_ctor_get_uint8(x_112, 14);
x_127 = lean_ctor_get_uint8(x_112, 15);
x_128 = lean_ctor_get_uint8(x_112, 16);
x_129 = lean_ctor_get_uint8(x_112, 17);
lean_dec(x_112);
x_130 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_130, 0, x_113);
lean_ctor_set_uint8(x_130, 1, x_114);
lean_ctor_set_uint8(x_130, 2, x_115);
lean_ctor_set_uint8(x_130, 3, x_116);
lean_ctor_set_uint8(x_130, 4, x_117);
lean_ctor_set_uint8(x_130, 5, x_118);
lean_ctor_set_uint8(x_130, 6, x_119);
lean_ctor_set_uint8(x_130, 7, x_120);
lean_ctor_set_uint8(x_130, 8, x_121);
x_131 = lean_unbox(x_111);
lean_ctor_set_uint8(x_130, 9, x_131);
lean_ctor_set_uint8(x_130, 10, x_122);
lean_ctor_set_uint8(x_130, 11, x_123);
lean_ctor_set_uint8(x_130, 12, x_124);
lean_ctor_set_uint8(x_130, 13, x_125);
lean_ctor_set_uint8(x_130, 14, x_126);
lean_ctor_set_uint8(x_130, 15, x_127);
lean_ctor_set_uint8(x_130, 16, x_128);
lean_ctor_set_uint8(x_130, 17, x_129);
x_132 = lean_ctor_get_uint64(x_106, sizeof(void*)*7);
x_133 = lean_unsigned_to_nat(2u);
x_134 = lean_uint64_of_nat(x_133);
x_135 = lean_uint64_shift_right(x_132, x_134);
x_136 = lean_uint64_shift_left(x_135, x_134);
x_137 = lean_unbox(x_111);
x_138 = l_Lean_Meta_TransparencyMode_toUInt64(x_137);
x_139 = lean_uint64_lor(x_136, x_138);
x_140 = lean_ctor_get_uint8(x_106, sizeof(void*)*7 + 8);
x_141 = lean_ctor_get(x_106, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_106, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_106, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_106, 4);
lean_inc(x_144);
x_145 = lean_ctor_get(x_106, 5);
lean_inc(x_145);
x_146 = lean_ctor_get(x_106, 6);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_106, sizeof(void*)*7 + 9);
x_148 = lean_ctor_get_uint8(x_106, sizeof(void*)*7 + 10);
x_149 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_149, 0, x_130);
lean_ctor_set(x_149, 1, x_141);
lean_ctor_set(x_149, 2, x_142);
lean_ctor_set(x_149, 3, x_143);
lean_ctor_set(x_149, 4, x_144);
lean_ctor_set(x_149, 5, x_145);
lean_ctor_set(x_149, 6, x_146);
lean_ctor_set_uint64(x_149, sizeof(void*)*7, x_139);
lean_ctor_set_uint8(x_149, sizeof(void*)*7 + 8, x_140);
lean_ctor_set_uint8(x_149, sizeof(void*)*7 + 9, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*7 + 10, x_148);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_100);
x_150 = l_Lean_Meta_isExprDefEq(x_100, x_97, x_149, x_107, x_108, x_109, x_110);
lean_dec(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
uint8_t x_153; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_153 = !lean_is_exclusive(x_150);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_150, 0);
lean_dec(x_154);
x_155 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_92;
}
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_98)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_98;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_35);
lean_ctor_set(x_150, 0, x_157);
return x_150;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_150, 1);
lean_inc(x_158);
lean_dec(x_150);
x_159 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_92;
}
lean_ctor_set(x_160, 0, x_159);
if (lean_is_scalar(x_98)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_98;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_35);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_158);
return x_162;
}
}
else
{
lean_dec(x_98);
lean_dec(x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_150, 1);
lean_inc(x_163);
lean_dec(x_150);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
x_164 = l_Lean_Meta_Grind_proveEq_x3f(x_96, x_100, x_102, x_103, x_104, x_105, x_106, x_107, x_108, x_109, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_38 = x_165;
x_39 = x_106;
x_40 = x_107;
x_41 = x_108;
x_42 = x_109;
x_43 = x_166;
goto block_82;
}
else
{
uint8_t x_167; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_167 = !lean_is_exclusive(x_164);
if (x_167 == 0)
{
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_164);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_95);
x_171 = lean_ctor_get(x_150, 1);
lean_inc(x_171);
lean_dec(x_150);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
x_172 = l_Lean_Meta_Grind_proveHEq_x3f(x_96, x_100, x_102, x_103, x_104, x_105, x_106, x_107, x_108, x_109, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_38 = x_173;
x_39 = x_106;
x_40 = x_107;
x_41 = x_108;
x_42 = x_109;
x_43 = x_174;
goto block_82;
}
else
{
uint8_t x_175; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_175 = !lean_is_exclusive(x_172);
if (x_175 == 0)
{
return x_172;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_172, 0);
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_172);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_179 = !lean_is_exclusive(x_150);
if (x_179 == 0)
{
return x_150;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_150, 0);
x_181 = lean_ctor_get(x_150, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_150);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_free_object(x_91);
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_218 = !lean_is_exclusive(x_99);
if (x_218 == 0)
{
return x_99;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_99, 0);
x_220 = lean_ctor_get(x_99, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_99);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_91, 1);
x_223 = lean_ctor_get(x_91, 0);
lean_inc(x_222);
lean_inc(x_223);
lean_dec(x_91);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_224);
x_227 = l_Lean_Meta_Grind_tryToProveFalse_go(x_224, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_86);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_308 = lean_mk_string_unchecked("grind", 5, 5);
x_309 = lean_mk_string_unchecked("debug", 5, 5);
x_310 = lean_mk_string_unchecked("matchCond", 9, 9);
x_311 = lean_mk_string_unchecked("proveFalse", 10, 10);
x_312 = l_Lean_Name_mkStr4(x_308, x_309, x_310, x_311);
lean_inc(x_312);
x_313 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_312, x_11, x_229);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_unbox(x_314);
lean_dec(x_314);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec(x_312);
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
lean_dec(x_313);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_230 = x_5;
x_231 = x_6;
x_232 = x_7;
x_233 = x_8;
x_234 = x_9;
x_235 = x_10;
x_236 = x_11;
x_237 = x_12;
x_238 = x_316;
goto block_307;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_317 = lean_ctor_get(x_313, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_318 = x_313;
} else {
 lean_dec_ref(x_313);
 x_318 = lean_box(0);
}
x_319 = lean_mk_string_unchecked("", 0, 0);
x_320 = l_Lean_stringToMessageData(x_319);
lean_dec(x_319);
lean_inc(x_228);
x_321 = l_Lean_MessageData_ofExpr(x_228);
lean_inc(x_320);
if (lean_is_scalar(x_318)) {
 x_322 = lean_alloc_ctor(7, 2, 0);
} else {
 x_322 = x_318;
 lean_ctor_set_tag(x_322, 7);
}
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_324 = l_Lean_stringToMessageData(x_323);
lean_dec(x_323);
x_325 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_324);
lean_inc(x_225);
x_326 = l_Lean_MessageData_ofExpr(x_225);
x_327 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_320);
x_329 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_312, x_328, x_9, x_10, x_11, x_12, x_317);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_230 = x_5;
x_231 = x_6;
x_232 = x_7;
x_233 = x_8;
x_234 = x_9;
x_235 = x_10;
x_236 = x_11;
x_237 = x_12;
x_238 = x_330;
goto block_307;
}
block_307:
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; uint8_t x_255; uint8_t x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; uint64_t x_260; lean_object* x_261; uint64_t x_262; uint64_t x_263; uint64_t x_264; uint8_t x_265; uint64_t x_266; uint64_t x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; 
x_239 = lean_box(1);
x_240 = lean_ctor_get(x_234, 0);
lean_inc(x_240);
x_241 = lean_ctor_get_uint8(x_240, 0);
x_242 = lean_ctor_get_uint8(x_240, 1);
x_243 = lean_ctor_get_uint8(x_240, 2);
x_244 = lean_ctor_get_uint8(x_240, 3);
x_245 = lean_ctor_get_uint8(x_240, 4);
x_246 = lean_ctor_get_uint8(x_240, 5);
x_247 = lean_ctor_get_uint8(x_240, 6);
x_248 = lean_ctor_get_uint8(x_240, 7);
x_249 = lean_ctor_get_uint8(x_240, 8);
x_250 = lean_ctor_get_uint8(x_240, 10);
x_251 = lean_ctor_get_uint8(x_240, 11);
x_252 = lean_ctor_get_uint8(x_240, 12);
x_253 = lean_ctor_get_uint8(x_240, 13);
x_254 = lean_ctor_get_uint8(x_240, 14);
x_255 = lean_ctor_get_uint8(x_240, 15);
x_256 = lean_ctor_get_uint8(x_240, 16);
x_257 = lean_ctor_get_uint8(x_240, 17);
lean_dec(x_240);
x_258 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_258, 0, x_241);
lean_ctor_set_uint8(x_258, 1, x_242);
lean_ctor_set_uint8(x_258, 2, x_243);
lean_ctor_set_uint8(x_258, 3, x_244);
lean_ctor_set_uint8(x_258, 4, x_245);
lean_ctor_set_uint8(x_258, 5, x_246);
lean_ctor_set_uint8(x_258, 6, x_247);
lean_ctor_set_uint8(x_258, 7, x_248);
lean_ctor_set_uint8(x_258, 8, x_249);
x_259 = lean_unbox(x_239);
lean_ctor_set_uint8(x_258, 9, x_259);
lean_ctor_set_uint8(x_258, 10, x_250);
lean_ctor_set_uint8(x_258, 11, x_251);
lean_ctor_set_uint8(x_258, 12, x_252);
lean_ctor_set_uint8(x_258, 13, x_253);
lean_ctor_set_uint8(x_258, 14, x_254);
lean_ctor_set_uint8(x_258, 15, x_255);
lean_ctor_set_uint8(x_258, 16, x_256);
lean_ctor_set_uint8(x_258, 17, x_257);
x_260 = lean_ctor_get_uint64(x_234, sizeof(void*)*7);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_uint64_of_nat(x_261);
x_263 = lean_uint64_shift_right(x_260, x_262);
x_264 = lean_uint64_shift_left(x_263, x_262);
x_265 = lean_unbox(x_239);
x_266 = l_Lean_Meta_TransparencyMode_toUInt64(x_265);
x_267 = lean_uint64_lor(x_264, x_266);
x_268 = lean_ctor_get_uint8(x_234, sizeof(void*)*7 + 8);
x_269 = lean_ctor_get(x_234, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_234, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_234, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_234, 4);
lean_inc(x_272);
x_273 = lean_ctor_get(x_234, 5);
lean_inc(x_273);
x_274 = lean_ctor_get(x_234, 6);
lean_inc(x_274);
x_275 = lean_ctor_get_uint8(x_234, sizeof(void*)*7 + 9);
x_276 = lean_ctor_get_uint8(x_234, sizeof(void*)*7 + 10);
x_277 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_277, 0, x_258);
lean_ctor_set(x_277, 1, x_269);
lean_ctor_set(x_277, 2, x_270);
lean_ctor_set(x_277, 3, x_271);
lean_ctor_set(x_277, 4, x_272);
lean_ctor_set(x_277, 5, x_273);
lean_ctor_set(x_277, 6, x_274);
lean_ctor_set_uint64(x_277, sizeof(void*)*7, x_267);
lean_ctor_set_uint8(x_277, sizeof(void*)*7 + 8, x_268);
lean_ctor_set_uint8(x_277, sizeof(void*)*7 + 9, x_275);
lean_ctor_set_uint8(x_277, sizeof(void*)*7 + 10, x_276);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_228);
x_278 = l_Lean_Meta_isExprDefEq(x_228, x_225, x_277, x_235, x_236, x_237, x_238);
lean_dec(x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_unbox(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_282 = x_278;
} else {
 lean_dec_ref(x_278);
 x_282 = lean_box(0);
}
x_283 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_284 = lean_alloc_ctor(1, 1, 0);
} else {
 x_284 = x_92;
}
lean_ctor_set(x_284, 0, x_283);
if (lean_is_scalar(x_226)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_226;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_35);
if (lean_is_scalar(x_282)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_282;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_281);
return x_286;
}
else
{
lean_dec(x_226);
lean_dec(x_92);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_278, 1);
lean_inc(x_287);
lean_dec(x_278);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
x_288 = l_Lean_Meta_Grind_proveEq_x3f(x_224, x_228, x_230, x_231, x_232, x_233, x_234, x_235, x_236, x_237, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_38 = x_289;
x_39 = x_234;
x_40 = x_235;
x_41 = x_236;
x_42 = x_237;
x_43 = x_290;
goto block_82;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_291 = lean_ctor_get(x_288, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_293 = x_288;
} else {
 lean_dec_ref(x_288);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_223);
x_295 = lean_ctor_get(x_278, 1);
lean_inc(x_295);
lean_dec(x_278);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
x_296 = l_Lean_Meta_Grind_proveHEq_x3f(x_224, x_228, x_230, x_231, x_232, x_233, x_234, x_235, x_236, x_237, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_38 = x_297;
x_39 = x_234;
x_40 = x_235;
x_41 = x_236;
x_42 = x_237;
x_43 = x_298;
goto block_82;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_299 = lean_ctor_get(x_296, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_301 = x_296;
} else {
 lean_dec_ref(x_296);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_92);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_303 = lean_ctor_get(x_278, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_278, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_305 = x_278;
} else {
 lean_dec_ref(x_278);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_92);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_331 = lean_ctor_get(x_227, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_227, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_333 = x_227;
} else {
 lean_dec_ref(x_227);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_83, 0);
x_336 = lean_ctor_get(x_83, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_83);
x_337 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_335);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_338 = lean_box(0);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_35);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_336);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_342 = lean_ctor_get(x_337, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_343 = x_337;
} else {
 lean_dec_ref(x_337);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_346 = x_342;
} else {
 lean_dec_ref(x_342);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_344, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_349 = x_344;
} else {
 lean_dec_ref(x_344);
 x_349 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_347);
x_350 = l_Lean_Meta_Grind_tryToProveFalse_go(x_347, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_336);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_431 = lean_mk_string_unchecked("grind", 5, 5);
x_432 = lean_mk_string_unchecked("debug", 5, 5);
x_433 = lean_mk_string_unchecked("matchCond", 9, 9);
x_434 = lean_mk_string_unchecked("proveFalse", 10, 10);
x_435 = l_Lean_Name_mkStr4(x_431, x_432, x_433, x_434);
lean_inc(x_435);
x_436 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_435, x_11, x_352);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_unbox(x_437);
lean_dec(x_437);
if (x_438 == 0)
{
lean_object* x_439; 
lean_dec(x_435);
lean_dec(x_346);
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_dec(x_436);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_353 = x_5;
x_354 = x_6;
x_355 = x_7;
x_356 = x_8;
x_357 = x_9;
x_358 = x_10;
x_359 = x_11;
x_360 = x_12;
x_361 = x_439;
goto block_430;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_440 = lean_ctor_get(x_436, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_441 = x_436;
} else {
 lean_dec_ref(x_436);
 x_441 = lean_box(0);
}
x_442 = lean_mk_string_unchecked("", 0, 0);
x_443 = l_Lean_stringToMessageData(x_442);
lean_dec(x_442);
lean_inc(x_351);
x_444 = l_Lean_MessageData_ofExpr(x_351);
lean_inc(x_443);
if (lean_is_scalar(x_441)) {
 x_445 = lean_alloc_ctor(7, 2, 0);
} else {
 x_445 = x_441;
 lean_ctor_set_tag(x_445, 7);
}
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_447 = l_Lean_stringToMessageData(x_446);
lean_dec(x_446);
if (lean_is_scalar(x_346)) {
 x_448 = lean_alloc_ctor(7, 2, 0);
} else {
 x_448 = x_346;
 lean_ctor_set_tag(x_448, 7);
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_447);
lean_inc(x_348);
x_449 = l_Lean_MessageData_ofExpr(x_348);
x_450 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_443);
x_452 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_435, x_451, x_9, x_10, x_11, x_12, x_440);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
lean_dec(x_452);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_353 = x_5;
x_354 = x_6;
x_355 = x_7;
x_356 = x_8;
x_357 = x_9;
x_358 = x_10;
x_359 = x_11;
x_360 = x_12;
x_361 = x_453;
goto block_430;
}
block_430:
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_365; uint8_t x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; uint8_t x_370; uint8_t x_371; uint8_t x_372; uint8_t x_373; uint8_t x_374; uint8_t x_375; uint8_t x_376; uint8_t x_377; uint8_t x_378; uint8_t x_379; uint8_t x_380; lean_object* x_381; uint8_t x_382; uint64_t x_383; lean_object* x_384; uint64_t x_385; uint64_t x_386; uint64_t x_387; uint8_t x_388; uint64_t x_389; uint64_t x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; uint8_t x_399; lean_object* x_400; lean_object* x_401; 
x_362 = lean_box(1);
x_363 = lean_ctor_get(x_357, 0);
lean_inc(x_363);
x_364 = lean_ctor_get_uint8(x_363, 0);
x_365 = lean_ctor_get_uint8(x_363, 1);
x_366 = lean_ctor_get_uint8(x_363, 2);
x_367 = lean_ctor_get_uint8(x_363, 3);
x_368 = lean_ctor_get_uint8(x_363, 4);
x_369 = lean_ctor_get_uint8(x_363, 5);
x_370 = lean_ctor_get_uint8(x_363, 6);
x_371 = lean_ctor_get_uint8(x_363, 7);
x_372 = lean_ctor_get_uint8(x_363, 8);
x_373 = lean_ctor_get_uint8(x_363, 10);
x_374 = lean_ctor_get_uint8(x_363, 11);
x_375 = lean_ctor_get_uint8(x_363, 12);
x_376 = lean_ctor_get_uint8(x_363, 13);
x_377 = lean_ctor_get_uint8(x_363, 14);
x_378 = lean_ctor_get_uint8(x_363, 15);
x_379 = lean_ctor_get_uint8(x_363, 16);
x_380 = lean_ctor_get_uint8(x_363, 17);
lean_dec(x_363);
x_381 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_381, 0, x_364);
lean_ctor_set_uint8(x_381, 1, x_365);
lean_ctor_set_uint8(x_381, 2, x_366);
lean_ctor_set_uint8(x_381, 3, x_367);
lean_ctor_set_uint8(x_381, 4, x_368);
lean_ctor_set_uint8(x_381, 5, x_369);
lean_ctor_set_uint8(x_381, 6, x_370);
lean_ctor_set_uint8(x_381, 7, x_371);
lean_ctor_set_uint8(x_381, 8, x_372);
x_382 = lean_unbox(x_362);
lean_ctor_set_uint8(x_381, 9, x_382);
lean_ctor_set_uint8(x_381, 10, x_373);
lean_ctor_set_uint8(x_381, 11, x_374);
lean_ctor_set_uint8(x_381, 12, x_375);
lean_ctor_set_uint8(x_381, 13, x_376);
lean_ctor_set_uint8(x_381, 14, x_377);
lean_ctor_set_uint8(x_381, 15, x_378);
lean_ctor_set_uint8(x_381, 16, x_379);
lean_ctor_set_uint8(x_381, 17, x_380);
x_383 = lean_ctor_get_uint64(x_357, sizeof(void*)*7);
x_384 = lean_unsigned_to_nat(2u);
x_385 = lean_uint64_of_nat(x_384);
x_386 = lean_uint64_shift_right(x_383, x_385);
x_387 = lean_uint64_shift_left(x_386, x_385);
x_388 = lean_unbox(x_362);
x_389 = l_Lean_Meta_TransparencyMode_toUInt64(x_388);
x_390 = lean_uint64_lor(x_387, x_389);
x_391 = lean_ctor_get_uint8(x_357, sizeof(void*)*7 + 8);
x_392 = lean_ctor_get(x_357, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_357, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_357, 3);
lean_inc(x_394);
x_395 = lean_ctor_get(x_357, 4);
lean_inc(x_395);
x_396 = lean_ctor_get(x_357, 5);
lean_inc(x_396);
x_397 = lean_ctor_get(x_357, 6);
lean_inc(x_397);
x_398 = lean_ctor_get_uint8(x_357, sizeof(void*)*7 + 9);
x_399 = lean_ctor_get_uint8(x_357, sizeof(void*)*7 + 10);
x_400 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_400, 0, x_381);
lean_ctor_set(x_400, 1, x_392);
lean_ctor_set(x_400, 2, x_393);
lean_ctor_set(x_400, 3, x_394);
lean_ctor_set(x_400, 4, x_395);
lean_ctor_set(x_400, 5, x_396);
lean_ctor_set(x_400, 6, x_397);
lean_ctor_set_uint64(x_400, sizeof(void*)*7, x_390);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 8, x_391);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 9, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 10, x_399);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_351);
x_401 = l_Lean_Meta_isExprDefEq(x_351, x_348, x_400, x_358, x_359, x_360, x_361);
lean_dec(x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; uint8_t x_403; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_unbox(x_402);
lean_dec(x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_405 = x_401;
} else {
 lean_dec_ref(x_401);
 x_405 = lean_box(0);
}
x_406 = lean_box(0);
if (lean_is_scalar(x_343)) {
 x_407 = lean_alloc_ctor(1, 1, 0);
} else {
 x_407 = x_343;
}
lean_ctor_set(x_407, 0, x_406);
if (lean_is_scalar(x_349)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_349;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_35);
if (lean_is_scalar(x_405)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_405;
}
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_404);
return x_409;
}
else
{
lean_dec(x_349);
lean_dec(x_343);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_401, 1);
lean_inc(x_410);
lean_dec(x_401);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
x_411 = l_Lean_Meta_Grind_proveEq_x3f(x_347, x_351, x_353, x_354, x_355, x_356, x_357, x_358, x_359, x_360, x_410);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_38 = x_412;
x_39 = x_357;
x_40 = x_358;
x_41 = x_359;
x_42 = x_360;
x_43 = x_413;
goto block_82;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_414 = lean_ctor_get(x_411, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_411, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_416 = x_411;
} else {
 lean_dec_ref(x_411);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; 
lean_dec(x_345);
x_418 = lean_ctor_get(x_401, 1);
lean_inc(x_418);
lean_dec(x_401);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
x_419 = l_Lean_Meta_Grind_proveHEq_x3f(x_347, x_351, x_353, x_354, x_355, x_356, x_357, x_358, x_359, x_360, x_418);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_38 = x_420;
x_39 = x_357;
x_40 = x_358;
x_41 = x_359;
x_42 = x_360;
x_43 = x_421;
goto block_82;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_422 = lean_ctor_get(x_419, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_424 = x_419;
} else {
 lean_dec_ref(x_419);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_426 = lean_ctor_get(x_401, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_401, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_428 = x_401;
} else {
 lean_dec_ref(x_401);
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
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_454 = lean_ctor_get(x_350, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_350, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_456 = x_350;
} else {
 lean_dec_ref(x_350);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
return x_457;
}
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_458 = !lean_is_exclusive(x_83);
if (x_458 == 0)
{
return x_83;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_83, 0);
x_460 = lean_ctor_get(x_83, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_83);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
block_82:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_38);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = l_Lean_Meta_isExprDefEq(x_37, x_48, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_39);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_38, 0, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_box(0);
lean_ctor_set(x_38, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_35);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_38);
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_dec(x_49);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_23);
lean_ctor_set(x_61, 1, x_35);
x_14 = x_61;
x_15 = x_60;
goto block_20;
}
}
else
{
uint8_t x_62; 
lean_free_object(x_38);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_49);
if (x_62 == 0)
{
return x_49;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_49, 0);
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_49);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_38, 0);
lean_inc(x_66);
lean_dec(x_38);
x_67 = l_Lean_Meta_isExprDefEq(x_37, x_66, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_39);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_35);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_dec(x_67);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_23);
lean_ctor_set(x_77, 1, x_35);
x_14 = x_77;
x_15 = x_76;
goto block_20;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_80 = x_67;
} else {
 lean_dec_ref(x_67);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_14;
x_13 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_3, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_array_fget(x_30, x_25);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_25, x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_26);
if (x_32 == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
x_14 = x_36;
x_15 = x_13;
goto block_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_83; 
x_37 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_37);
x_83 = lean_infer_type(x_37, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
x_87 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_35);
lean_ctor_set(x_83, 0, x_90);
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_free_object(x_83);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_91, 1);
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_96);
x_99 = l_Lean_Meta_Grind_tryToProveFalse_go(x_96, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_86);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_184 = lean_mk_string_unchecked("grind", 5, 5);
x_185 = lean_mk_string_unchecked("debug", 5, 5);
x_186 = lean_mk_string_unchecked("matchCond", 9, 9);
x_187 = lean_mk_string_unchecked("proveFalse", 10, 10);
x_188 = l_Lean_Name_mkStr4(x_184, x_185, x_186, x_187);
lean_inc(x_188);
x_189 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_188, x_11, x_101);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
lean_dec(x_188);
lean_free_object(x_91);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_192;
goto block_183;
}
else
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_189);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_194 = lean_ctor_get(x_189, 1);
x_195 = lean_ctor_get(x_189, 0);
lean_dec(x_195);
x_196 = lean_mk_string_unchecked("", 0, 0);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
lean_inc(x_100);
x_198 = l_Lean_MessageData_ofExpr(x_100);
lean_inc(x_197);
lean_ctor_set_tag(x_189, 7);
lean_ctor_set(x_189, 1, x_198);
lean_ctor_set(x_189, 0, x_197);
x_199 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_200 = l_Lean_stringToMessageData(x_199);
lean_dec(x_199);
lean_ctor_set_tag(x_91, 7);
lean_ctor_set(x_91, 1, x_200);
lean_ctor_set(x_91, 0, x_189);
lean_inc(x_97);
x_201 = l_Lean_MessageData_ofExpr(x_97);
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_91);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_197);
x_204 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_188, x_203, x_9, x_10, x_11, x_12, x_194);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_205;
goto block_183;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_206 = lean_ctor_get(x_189, 1);
lean_inc(x_206);
lean_dec(x_189);
x_207 = lean_mk_string_unchecked("", 0, 0);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
lean_inc(x_100);
x_209 = l_Lean_MessageData_ofExpr(x_100);
lean_inc(x_208);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
lean_ctor_set_tag(x_91, 7);
lean_ctor_set(x_91, 1, x_212);
lean_ctor_set(x_91, 0, x_210);
lean_inc(x_97);
x_213 = l_Lean_MessageData_ofExpr(x_97);
x_214 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_214, 0, x_91);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_208);
x_216 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_188, x_215, x_9, x_10, x_11, x_12, x_206);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = x_5;
x_103 = x_6;
x_104 = x_7;
x_105 = x_8;
x_106 = x_9;
x_107 = x_10;
x_108 = x_11;
x_109 = x_12;
x_110 = x_217;
goto block_183;
}
}
block_183:
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; uint64_t x_132; lean_object* x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint8_t x_137; uint64_t x_138; uint64_t x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
x_111 = lean_box(1);
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
x_113 = lean_ctor_get_uint8(x_112, 0);
x_114 = lean_ctor_get_uint8(x_112, 1);
x_115 = lean_ctor_get_uint8(x_112, 2);
x_116 = lean_ctor_get_uint8(x_112, 3);
x_117 = lean_ctor_get_uint8(x_112, 4);
x_118 = lean_ctor_get_uint8(x_112, 5);
x_119 = lean_ctor_get_uint8(x_112, 6);
x_120 = lean_ctor_get_uint8(x_112, 7);
x_121 = lean_ctor_get_uint8(x_112, 8);
x_122 = lean_ctor_get_uint8(x_112, 10);
x_123 = lean_ctor_get_uint8(x_112, 11);
x_124 = lean_ctor_get_uint8(x_112, 12);
x_125 = lean_ctor_get_uint8(x_112, 13);
x_126 = lean_ctor_get_uint8(x_112, 14);
x_127 = lean_ctor_get_uint8(x_112, 15);
x_128 = lean_ctor_get_uint8(x_112, 16);
x_129 = lean_ctor_get_uint8(x_112, 17);
lean_dec(x_112);
x_130 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_130, 0, x_113);
lean_ctor_set_uint8(x_130, 1, x_114);
lean_ctor_set_uint8(x_130, 2, x_115);
lean_ctor_set_uint8(x_130, 3, x_116);
lean_ctor_set_uint8(x_130, 4, x_117);
lean_ctor_set_uint8(x_130, 5, x_118);
lean_ctor_set_uint8(x_130, 6, x_119);
lean_ctor_set_uint8(x_130, 7, x_120);
lean_ctor_set_uint8(x_130, 8, x_121);
x_131 = lean_unbox(x_111);
lean_ctor_set_uint8(x_130, 9, x_131);
lean_ctor_set_uint8(x_130, 10, x_122);
lean_ctor_set_uint8(x_130, 11, x_123);
lean_ctor_set_uint8(x_130, 12, x_124);
lean_ctor_set_uint8(x_130, 13, x_125);
lean_ctor_set_uint8(x_130, 14, x_126);
lean_ctor_set_uint8(x_130, 15, x_127);
lean_ctor_set_uint8(x_130, 16, x_128);
lean_ctor_set_uint8(x_130, 17, x_129);
x_132 = lean_ctor_get_uint64(x_106, sizeof(void*)*7);
x_133 = lean_unsigned_to_nat(2u);
x_134 = lean_uint64_of_nat(x_133);
x_135 = lean_uint64_shift_right(x_132, x_134);
x_136 = lean_uint64_shift_left(x_135, x_134);
x_137 = lean_unbox(x_111);
x_138 = l_Lean_Meta_TransparencyMode_toUInt64(x_137);
x_139 = lean_uint64_lor(x_136, x_138);
x_140 = lean_ctor_get_uint8(x_106, sizeof(void*)*7 + 8);
x_141 = lean_ctor_get(x_106, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_106, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_106, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_106, 4);
lean_inc(x_144);
x_145 = lean_ctor_get(x_106, 5);
lean_inc(x_145);
x_146 = lean_ctor_get(x_106, 6);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_106, sizeof(void*)*7 + 9);
x_148 = lean_ctor_get_uint8(x_106, sizeof(void*)*7 + 10);
x_149 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_149, 0, x_130);
lean_ctor_set(x_149, 1, x_141);
lean_ctor_set(x_149, 2, x_142);
lean_ctor_set(x_149, 3, x_143);
lean_ctor_set(x_149, 4, x_144);
lean_ctor_set(x_149, 5, x_145);
lean_ctor_set(x_149, 6, x_146);
lean_ctor_set_uint64(x_149, sizeof(void*)*7, x_139);
lean_ctor_set_uint8(x_149, sizeof(void*)*7 + 8, x_140);
lean_ctor_set_uint8(x_149, sizeof(void*)*7 + 9, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*7 + 10, x_148);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_100);
x_150 = l_Lean_Meta_isExprDefEq(x_100, x_97, x_149, x_107, x_108, x_109, x_110);
lean_dec(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
uint8_t x_153; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_153 = !lean_is_exclusive(x_150);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_150, 0);
lean_dec(x_154);
x_155 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_92;
}
lean_ctor_set(x_156, 0, x_155);
if (lean_is_scalar(x_98)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_98;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_35);
lean_ctor_set(x_150, 0, x_157);
return x_150;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_150, 1);
lean_inc(x_158);
lean_dec(x_150);
x_159 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_92;
}
lean_ctor_set(x_160, 0, x_159);
if (lean_is_scalar(x_98)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_98;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_35);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_158);
return x_162;
}
}
else
{
lean_dec(x_98);
lean_dec(x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_150, 1);
lean_inc(x_163);
lean_dec(x_150);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
x_164 = l_Lean_Meta_Grind_proveEq_x3f(x_96, x_100, x_102, x_103, x_104, x_105, x_106, x_107, x_108, x_109, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_38 = x_165;
x_39 = x_106;
x_40 = x_107;
x_41 = x_108;
x_42 = x_109;
x_43 = x_166;
goto block_82;
}
else
{
uint8_t x_167; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_167 = !lean_is_exclusive(x_164);
if (x_167 == 0)
{
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_164, 0);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_164);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_95);
x_171 = lean_ctor_get(x_150, 1);
lean_inc(x_171);
lean_dec(x_150);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
x_172 = l_Lean_Meta_Grind_proveHEq_x3f(x_96, x_100, x_102, x_103, x_104, x_105, x_106, x_107, x_108, x_109, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_38 = x_173;
x_39 = x_106;
x_40 = x_107;
x_41 = x_108;
x_42 = x_109;
x_43 = x_174;
goto block_82;
}
else
{
uint8_t x_175; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_175 = !lean_is_exclusive(x_172);
if (x_175 == 0)
{
return x_172;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_172, 0);
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_172);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_179 = !lean_is_exclusive(x_150);
if (x_179 == 0)
{
return x_150;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_150, 0);
x_181 = lean_ctor_get(x_150, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_150);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_free_object(x_91);
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_218 = !lean_is_exclusive(x_99);
if (x_218 == 0)
{
return x_99;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_99, 0);
x_220 = lean_ctor_get(x_99, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_99);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_91, 1);
x_223 = lean_ctor_get(x_91, 0);
lean_inc(x_222);
lean_inc(x_223);
lean_dec(x_91);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_224);
x_227 = l_Lean_Meta_Grind_tryToProveFalse_go(x_224, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_86);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_308 = lean_mk_string_unchecked("grind", 5, 5);
x_309 = lean_mk_string_unchecked("debug", 5, 5);
x_310 = lean_mk_string_unchecked("matchCond", 9, 9);
x_311 = lean_mk_string_unchecked("proveFalse", 10, 10);
x_312 = l_Lean_Name_mkStr4(x_308, x_309, x_310, x_311);
lean_inc(x_312);
x_313 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_312, x_11, x_229);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_unbox(x_314);
lean_dec(x_314);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec(x_312);
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
lean_dec(x_313);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_230 = x_5;
x_231 = x_6;
x_232 = x_7;
x_233 = x_8;
x_234 = x_9;
x_235 = x_10;
x_236 = x_11;
x_237 = x_12;
x_238 = x_316;
goto block_307;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_317 = lean_ctor_get(x_313, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_318 = x_313;
} else {
 lean_dec_ref(x_313);
 x_318 = lean_box(0);
}
x_319 = lean_mk_string_unchecked("", 0, 0);
x_320 = l_Lean_stringToMessageData(x_319);
lean_dec(x_319);
lean_inc(x_228);
x_321 = l_Lean_MessageData_ofExpr(x_228);
lean_inc(x_320);
if (lean_is_scalar(x_318)) {
 x_322 = lean_alloc_ctor(7, 2, 0);
} else {
 x_322 = x_318;
 lean_ctor_set_tag(x_322, 7);
}
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_324 = l_Lean_stringToMessageData(x_323);
lean_dec(x_323);
x_325 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_324);
lean_inc(x_225);
x_326 = l_Lean_MessageData_ofExpr(x_225);
x_327 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_320);
x_329 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_312, x_328, x_9, x_10, x_11, x_12, x_317);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_230 = x_5;
x_231 = x_6;
x_232 = x_7;
x_233 = x_8;
x_234 = x_9;
x_235 = x_10;
x_236 = x_11;
x_237 = x_12;
x_238 = x_330;
goto block_307;
}
block_307:
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; uint8_t x_255; uint8_t x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; uint64_t x_260; lean_object* x_261; uint64_t x_262; uint64_t x_263; uint64_t x_264; uint8_t x_265; uint64_t x_266; uint64_t x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; 
x_239 = lean_box(1);
x_240 = lean_ctor_get(x_234, 0);
lean_inc(x_240);
x_241 = lean_ctor_get_uint8(x_240, 0);
x_242 = lean_ctor_get_uint8(x_240, 1);
x_243 = lean_ctor_get_uint8(x_240, 2);
x_244 = lean_ctor_get_uint8(x_240, 3);
x_245 = lean_ctor_get_uint8(x_240, 4);
x_246 = lean_ctor_get_uint8(x_240, 5);
x_247 = lean_ctor_get_uint8(x_240, 6);
x_248 = lean_ctor_get_uint8(x_240, 7);
x_249 = lean_ctor_get_uint8(x_240, 8);
x_250 = lean_ctor_get_uint8(x_240, 10);
x_251 = lean_ctor_get_uint8(x_240, 11);
x_252 = lean_ctor_get_uint8(x_240, 12);
x_253 = lean_ctor_get_uint8(x_240, 13);
x_254 = lean_ctor_get_uint8(x_240, 14);
x_255 = lean_ctor_get_uint8(x_240, 15);
x_256 = lean_ctor_get_uint8(x_240, 16);
x_257 = lean_ctor_get_uint8(x_240, 17);
lean_dec(x_240);
x_258 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_258, 0, x_241);
lean_ctor_set_uint8(x_258, 1, x_242);
lean_ctor_set_uint8(x_258, 2, x_243);
lean_ctor_set_uint8(x_258, 3, x_244);
lean_ctor_set_uint8(x_258, 4, x_245);
lean_ctor_set_uint8(x_258, 5, x_246);
lean_ctor_set_uint8(x_258, 6, x_247);
lean_ctor_set_uint8(x_258, 7, x_248);
lean_ctor_set_uint8(x_258, 8, x_249);
x_259 = lean_unbox(x_239);
lean_ctor_set_uint8(x_258, 9, x_259);
lean_ctor_set_uint8(x_258, 10, x_250);
lean_ctor_set_uint8(x_258, 11, x_251);
lean_ctor_set_uint8(x_258, 12, x_252);
lean_ctor_set_uint8(x_258, 13, x_253);
lean_ctor_set_uint8(x_258, 14, x_254);
lean_ctor_set_uint8(x_258, 15, x_255);
lean_ctor_set_uint8(x_258, 16, x_256);
lean_ctor_set_uint8(x_258, 17, x_257);
x_260 = lean_ctor_get_uint64(x_234, sizeof(void*)*7);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_uint64_of_nat(x_261);
x_263 = lean_uint64_shift_right(x_260, x_262);
x_264 = lean_uint64_shift_left(x_263, x_262);
x_265 = lean_unbox(x_239);
x_266 = l_Lean_Meta_TransparencyMode_toUInt64(x_265);
x_267 = lean_uint64_lor(x_264, x_266);
x_268 = lean_ctor_get_uint8(x_234, sizeof(void*)*7 + 8);
x_269 = lean_ctor_get(x_234, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_234, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_234, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_234, 4);
lean_inc(x_272);
x_273 = lean_ctor_get(x_234, 5);
lean_inc(x_273);
x_274 = lean_ctor_get(x_234, 6);
lean_inc(x_274);
x_275 = lean_ctor_get_uint8(x_234, sizeof(void*)*7 + 9);
x_276 = lean_ctor_get_uint8(x_234, sizeof(void*)*7 + 10);
x_277 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_277, 0, x_258);
lean_ctor_set(x_277, 1, x_269);
lean_ctor_set(x_277, 2, x_270);
lean_ctor_set(x_277, 3, x_271);
lean_ctor_set(x_277, 4, x_272);
lean_ctor_set(x_277, 5, x_273);
lean_ctor_set(x_277, 6, x_274);
lean_ctor_set_uint64(x_277, sizeof(void*)*7, x_267);
lean_ctor_set_uint8(x_277, sizeof(void*)*7 + 8, x_268);
lean_ctor_set_uint8(x_277, sizeof(void*)*7 + 9, x_275);
lean_ctor_set_uint8(x_277, sizeof(void*)*7 + 10, x_276);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_228);
x_278 = l_Lean_Meta_isExprDefEq(x_228, x_225, x_277, x_235, x_236, x_237, x_238);
lean_dec(x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_unbox(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_282 = x_278;
} else {
 lean_dec_ref(x_278);
 x_282 = lean_box(0);
}
x_283 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_284 = lean_alloc_ctor(1, 1, 0);
} else {
 x_284 = x_92;
}
lean_ctor_set(x_284, 0, x_283);
if (lean_is_scalar(x_226)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_226;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_35);
if (lean_is_scalar(x_282)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_282;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_281);
return x_286;
}
else
{
lean_dec(x_226);
lean_dec(x_92);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_278, 1);
lean_inc(x_287);
lean_dec(x_278);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
x_288 = l_Lean_Meta_Grind_proveEq_x3f(x_224, x_228, x_230, x_231, x_232, x_233, x_234, x_235, x_236, x_237, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_38 = x_289;
x_39 = x_234;
x_40 = x_235;
x_41 = x_236;
x_42 = x_237;
x_43 = x_290;
goto block_82;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_291 = lean_ctor_get(x_288, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_293 = x_288;
} else {
 lean_dec_ref(x_288);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_223);
x_295 = lean_ctor_get(x_278, 1);
lean_inc(x_295);
lean_dec(x_278);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
x_296 = l_Lean_Meta_Grind_proveHEq_x3f(x_224, x_228, x_230, x_231, x_232, x_233, x_234, x_235, x_236, x_237, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_38 = x_297;
x_39 = x_234;
x_40 = x_235;
x_41 = x_236;
x_42 = x_237;
x_43 = x_298;
goto block_82;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_299 = lean_ctor_get(x_296, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_301 = x_296;
} else {
 lean_dec_ref(x_296);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_92);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_303 = lean_ctor_get(x_278, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_278, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_305 = x_278;
} else {
 lean_dec_ref(x_278);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_92);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_331 = lean_ctor_get(x_227, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_227, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_333 = x_227;
} else {
 lean_dec_ref(x_227);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_83, 0);
x_336 = lean_ctor_get(x_83, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_83);
x_337 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_335);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_338 = lean_box(0);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_35);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_336);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_342 = lean_ctor_get(x_337, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_343 = x_337;
} else {
 lean_dec_ref(x_337);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_346 = x_342;
} else {
 lean_dec_ref(x_342);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_344, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_349 = x_344;
} else {
 lean_dec_ref(x_344);
 x_349 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_347);
x_350 = l_Lean_Meta_Grind_tryToProveFalse_go(x_347, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_336);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_431 = lean_mk_string_unchecked("grind", 5, 5);
x_432 = lean_mk_string_unchecked("debug", 5, 5);
x_433 = lean_mk_string_unchecked("matchCond", 9, 9);
x_434 = lean_mk_string_unchecked("proveFalse", 10, 10);
x_435 = l_Lean_Name_mkStr4(x_431, x_432, x_433, x_434);
lean_inc(x_435);
x_436 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_435, x_11, x_352);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_unbox(x_437);
lean_dec(x_437);
if (x_438 == 0)
{
lean_object* x_439; 
lean_dec(x_435);
lean_dec(x_346);
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_dec(x_436);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_353 = x_5;
x_354 = x_6;
x_355 = x_7;
x_356 = x_8;
x_357 = x_9;
x_358 = x_10;
x_359 = x_11;
x_360 = x_12;
x_361 = x_439;
goto block_430;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_440 = lean_ctor_get(x_436, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_441 = x_436;
} else {
 lean_dec_ref(x_436);
 x_441 = lean_box(0);
}
x_442 = lean_mk_string_unchecked("", 0, 0);
x_443 = l_Lean_stringToMessageData(x_442);
lean_dec(x_442);
lean_inc(x_351);
x_444 = l_Lean_MessageData_ofExpr(x_351);
lean_inc(x_443);
if (lean_is_scalar(x_441)) {
 x_445 = lean_alloc_ctor(7, 2, 0);
} else {
 x_445 = x_441;
 lean_ctor_set_tag(x_445, 7);
}
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_447 = l_Lean_stringToMessageData(x_446);
lean_dec(x_446);
if (lean_is_scalar(x_346)) {
 x_448 = lean_alloc_ctor(7, 2, 0);
} else {
 x_448 = x_346;
 lean_ctor_set_tag(x_448, 7);
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_447);
lean_inc(x_348);
x_449 = l_Lean_MessageData_ofExpr(x_348);
x_450 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_443);
x_452 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_435, x_451, x_9, x_10, x_11, x_12, x_440);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
lean_dec(x_452);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_353 = x_5;
x_354 = x_6;
x_355 = x_7;
x_356 = x_8;
x_357 = x_9;
x_358 = x_10;
x_359 = x_11;
x_360 = x_12;
x_361 = x_453;
goto block_430;
}
block_430:
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_365; uint8_t x_366; uint8_t x_367; uint8_t x_368; uint8_t x_369; uint8_t x_370; uint8_t x_371; uint8_t x_372; uint8_t x_373; uint8_t x_374; uint8_t x_375; uint8_t x_376; uint8_t x_377; uint8_t x_378; uint8_t x_379; uint8_t x_380; lean_object* x_381; uint8_t x_382; uint64_t x_383; lean_object* x_384; uint64_t x_385; uint64_t x_386; uint64_t x_387; uint8_t x_388; uint64_t x_389; uint64_t x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; uint8_t x_399; lean_object* x_400; lean_object* x_401; 
x_362 = lean_box(1);
x_363 = lean_ctor_get(x_357, 0);
lean_inc(x_363);
x_364 = lean_ctor_get_uint8(x_363, 0);
x_365 = lean_ctor_get_uint8(x_363, 1);
x_366 = lean_ctor_get_uint8(x_363, 2);
x_367 = lean_ctor_get_uint8(x_363, 3);
x_368 = lean_ctor_get_uint8(x_363, 4);
x_369 = lean_ctor_get_uint8(x_363, 5);
x_370 = lean_ctor_get_uint8(x_363, 6);
x_371 = lean_ctor_get_uint8(x_363, 7);
x_372 = lean_ctor_get_uint8(x_363, 8);
x_373 = lean_ctor_get_uint8(x_363, 10);
x_374 = lean_ctor_get_uint8(x_363, 11);
x_375 = lean_ctor_get_uint8(x_363, 12);
x_376 = lean_ctor_get_uint8(x_363, 13);
x_377 = lean_ctor_get_uint8(x_363, 14);
x_378 = lean_ctor_get_uint8(x_363, 15);
x_379 = lean_ctor_get_uint8(x_363, 16);
x_380 = lean_ctor_get_uint8(x_363, 17);
lean_dec(x_363);
x_381 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_381, 0, x_364);
lean_ctor_set_uint8(x_381, 1, x_365);
lean_ctor_set_uint8(x_381, 2, x_366);
lean_ctor_set_uint8(x_381, 3, x_367);
lean_ctor_set_uint8(x_381, 4, x_368);
lean_ctor_set_uint8(x_381, 5, x_369);
lean_ctor_set_uint8(x_381, 6, x_370);
lean_ctor_set_uint8(x_381, 7, x_371);
lean_ctor_set_uint8(x_381, 8, x_372);
x_382 = lean_unbox(x_362);
lean_ctor_set_uint8(x_381, 9, x_382);
lean_ctor_set_uint8(x_381, 10, x_373);
lean_ctor_set_uint8(x_381, 11, x_374);
lean_ctor_set_uint8(x_381, 12, x_375);
lean_ctor_set_uint8(x_381, 13, x_376);
lean_ctor_set_uint8(x_381, 14, x_377);
lean_ctor_set_uint8(x_381, 15, x_378);
lean_ctor_set_uint8(x_381, 16, x_379);
lean_ctor_set_uint8(x_381, 17, x_380);
x_383 = lean_ctor_get_uint64(x_357, sizeof(void*)*7);
x_384 = lean_unsigned_to_nat(2u);
x_385 = lean_uint64_of_nat(x_384);
x_386 = lean_uint64_shift_right(x_383, x_385);
x_387 = lean_uint64_shift_left(x_386, x_385);
x_388 = lean_unbox(x_362);
x_389 = l_Lean_Meta_TransparencyMode_toUInt64(x_388);
x_390 = lean_uint64_lor(x_387, x_389);
x_391 = lean_ctor_get_uint8(x_357, sizeof(void*)*7 + 8);
x_392 = lean_ctor_get(x_357, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_357, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_357, 3);
lean_inc(x_394);
x_395 = lean_ctor_get(x_357, 4);
lean_inc(x_395);
x_396 = lean_ctor_get(x_357, 5);
lean_inc(x_396);
x_397 = lean_ctor_get(x_357, 6);
lean_inc(x_397);
x_398 = lean_ctor_get_uint8(x_357, sizeof(void*)*7 + 9);
x_399 = lean_ctor_get_uint8(x_357, sizeof(void*)*7 + 10);
x_400 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_400, 0, x_381);
lean_ctor_set(x_400, 1, x_392);
lean_ctor_set(x_400, 2, x_393);
lean_ctor_set(x_400, 3, x_394);
lean_ctor_set(x_400, 4, x_395);
lean_ctor_set(x_400, 5, x_396);
lean_ctor_set(x_400, 6, x_397);
lean_ctor_set_uint64(x_400, sizeof(void*)*7, x_390);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 8, x_391);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 9, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*7 + 10, x_399);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_351);
x_401 = l_Lean_Meta_isExprDefEq(x_351, x_348, x_400, x_358, x_359, x_360, x_361);
lean_dec(x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; uint8_t x_403; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_unbox(x_402);
lean_dec(x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_405 = x_401;
} else {
 lean_dec_ref(x_401);
 x_405 = lean_box(0);
}
x_406 = lean_box(0);
if (lean_is_scalar(x_343)) {
 x_407 = lean_alloc_ctor(1, 1, 0);
} else {
 x_407 = x_343;
}
lean_ctor_set(x_407, 0, x_406);
if (lean_is_scalar(x_349)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_349;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_35);
if (lean_is_scalar(x_405)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_405;
}
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_404);
return x_409;
}
else
{
lean_dec(x_349);
lean_dec(x_343);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_401, 1);
lean_inc(x_410);
lean_dec(x_401);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
x_411 = l_Lean_Meta_Grind_proveEq_x3f(x_347, x_351, x_353, x_354, x_355, x_356, x_357, x_358, x_359, x_360, x_410);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_38 = x_412;
x_39 = x_357;
x_40 = x_358;
x_41 = x_359;
x_42 = x_360;
x_43 = x_413;
goto block_82;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_414 = lean_ctor_get(x_411, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_411, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_416 = x_411;
} else {
 lean_dec_ref(x_411);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; 
lean_dec(x_345);
x_418 = lean_ctor_get(x_401, 1);
lean_inc(x_418);
lean_dec(x_401);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
x_419 = l_Lean_Meta_Grind_proveHEq_x3f(x_347, x_351, x_353, x_354, x_355, x_356, x_357, x_358, x_359, x_360, x_418);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_38 = x_420;
x_39 = x_357;
x_40 = x_358;
x_41 = x_359;
x_42 = x_360;
x_43 = x_421;
goto block_82;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_422 = lean_ctor_get(x_419, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_424 = x_419;
} else {
 lean_dec_ref(x_419);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_426 = lean_ctor_get(x_401, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_401, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_428 = x_401;
} else {
 lean_dec_ref(x_401);
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
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_343);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_454 = lean_ctor_get(x_350, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_350, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_456 = x_350;
} else {
 lean_dec_ref(x_350);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
return x_457;
}
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_458 = !lean_is_exclusive(x_83);
if (x_458 == 0)
{
return x_83;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_83, 0);
x_460 = lean_ctor_get(x_83, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_83);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
block_82:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_38);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = l_Lean_Meta_isExprDefEq(x_37, x_48, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_39);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_38, 0, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_box(0);
lean_ctor_set(x_38, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_35);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_38);
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_dec(x_49);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_23);
lean_ctor_set(x_61, 1, x_35);
x_14 = x_61;
x_15 = x_60;
goto block_20;
}
}
else
{
uint8_t x_62; 
lean_free_object(x_38);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_49);
if (x_62 == 0)
{
return x_49;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_49, 0);
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_49);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_38, 0);
lean_inc(x_66);
lean_dec(x_38);
x_67 = l_Lean_Meta_isExprDefEq(x_37, x_66, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_39);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_35);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_dec(x_67);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_23);
lean_ctor_set(x_77, 1, x_35);
x_14 = x_77;
x_15 = x_76;
goto block_20;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_80 = x_67;
} else {
 lean_dec_ref(x_67);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0(x_1, x_2, x_18, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_7);
x_8 = l_Lean_MetavarContext_getDecl(x_7, x_1);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_box(x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_15);
x_16 = l_Lean_MetavarContext_getDecl(x_15, x_1);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(x_1, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_15 = l_instMonadEIO(lean_box(0));
x_16 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, lean_box(0));
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_29);
lean_inc(x_30);
lean_inc(x_27);
lean_inc(x_24);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_13);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_14);
x_33 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_24);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_27);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_30);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_11);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_12);
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
x_48 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_47);
x_49 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_48);
x_50 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_49);
x_51 = l_instInhabitedBool;
x_52 = lean_box(x_51);
x_53 = l_instInhabitedOfMonad___redArg(x_50, x_52);
x_54 = lean_panic_fn(x_53, x_1);
x_55 = lean_apply_9(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_55;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_16, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_free_object(x_11);
x_18 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_19 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_20 = lean_unsigned_to_nat(425u);
x_21 = lean_unsigned_to_nat(14u);
x_22 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_23 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_18, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
x_24 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3_spec__3(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_nat_dec_le(x_26, x_25);
lean_dec(x_25);
lean_dec(x_26);
x_28 = lean_box(x_27);
lean_ctor_set(x_11, 0, x_28);
return x_11;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
x_33 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_32, x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
x_34 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_35 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_36 = lean_unsigned_to_nat(425u);
x_37 = lean_unsigned_to_nat(14u);
x_38 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_40 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3_spec__3(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_nat_dec_le(x_42, x_41);
lean_dec(x_41);
lean_dec(x_42);
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_20; 
x_20 = l_Lean_Level_hasMVar(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(x_20);
lean_inc(x_11);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
x_12 = x_22;
x_13 = x_20;
x_14 = x_11;
goto block_19;
}
else
{
lean_object* x_23; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_unbox(x_24);
lean_dec(x_24);
x_12 = x_23;
x_13 = x_26;
x_14 = x_25;
goto block_19;
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
return x_23;
}
}
block_19:
{
if (x_13 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = l_Lean_Level_hasMVar(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_18;
}
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_Lean_Level_hasMVar(x_11);
if (x_12 == 0)
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
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
x_1 = x_11;
goto _start;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___lam__0(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___lam__0(x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
case 5:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_1 = x_14;
x_10 = x_18;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(x_22);
lean_inc(x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
x_14 = x_24;
x_15 = x_22;
x_16 = x_13;
goto block_21;
}
else
{
lean_object* x_25; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_unbox(x_26);
lean_dec(x_26);
x_14 = x_25;
x_15 = x_28;
x_16 = x_27;
goto block_21;
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
lean_dec(x_5);
return x_25;
}
}
block_21:
{
if (x_15 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = l_Lean_Expr_hasMVar(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_20;
}
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(x_11, x_7, x_10);
lean_dec(x_7);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = l_List_anyM___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__6(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
case 5:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_27; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_27 = l_Lean_Expr_hasMVar(x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(x_27);
lean_inc(x_10);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
x_19 = x_29;
x_20 = x_27;
x_21 = x_10;
goto block_26;
}
else
{
lean_object* x_30; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = lean_unbox(x_31);
lean_dec(x_31);
x_19 = x_30;
x_20 = x_33;
x_21 = x_32;
goto block_26;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_30;
}
}
block_26:
{
if (x_20 == 0)
{
uint8_t x_22; 
lean_dec(x_19);
x_22 = l_Lean_Expr_hasMVar(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
x_1 = x_18;
x_10 = x_21;
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
lean_dec(x_2);
return x_19;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_38 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___lam__0(x_34, x_35, x_36, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_38;
}
case 7:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_43 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___lam__0(x_39, x_40, x_41, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_43;
}
case 8:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_66; 
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 2);
x_46 = lean_ctor_get(x_1, 3);
x_66 = l_Lean_Expr_hasMVar(x_44);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(x_66);
lean_inc(x_10);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_10);
x_55 = x_68;
x_56 = x_66;
x_57 = x_10;
goto block_65;
}
else
{
lean_object* x_69; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_69 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_55 = x_69;
x_56 = x_72;
x_57 = x_71;
goto block_65;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_69;
}
}
block_54:
{
if (x_48 == 0)
{
uint8_t x_50; 
lean_dec(x_47);
x_50 = l_Lean_Expr_hasMVar(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
x_1 = x_46;
x_10 = x_49;
goto _start;
}
}
else
{
lean_dec(x_49);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_47;
}
}
block_65:
{
if (x_56 == 0)
{
uint8_t x_58; 
lean_dec(x_55);
x_58 = l_Lean_Expr_hasMVar(x_45);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_box(x_58);
lean_inc(x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_47 = x_60;
x_48 = x_58;
x_49 = x_57;
goto block_54;
}
else
{
lean_object* x_61; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_61 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_unbox(x_62);
lean_dec(x_62);
x_47 = x_61;
x_48 = x_64;
x_49 = x_63;
goto block_54;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_61;
}
}
}
else
{
lean_dec(x_57);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
}
}
case 10:
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_1, 1);
x_74 = l_Lean_Expr_hasMVar(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_10);
return x_76;
}
else
{
x_1 = x_73;
goto _start;
}
}
case 11:
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_1, 2);
x_79 = l_Lean_Expr_hasMVar(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_10);
return x_81;
}
else
{
x_1 = x_78;
goto _start;
}
}
default: 
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_10);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(x_2, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
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
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_forallMetaTelescope(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_16, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec(x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get_size(x_24);
x_27 = l_Array_toSubarray___redArg(x_24, x_25, x_26);
x_28 = lean_box(0);
lean_ctor_set(x_16, 1, x_27);
lean_ctor_set(x_16, 0, x_28);
x_29 = lean_array_size(x_19);
x_30 = lean_usize_of_nat(x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0(x_19, x_29, x_30, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_35 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_48; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_mkOfEqTrueCore(x_3, x_36);
x_39 = l_Lean_mkAppN(x_38, x_19);
lean_dec(x_19);
x_40 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_39, x_10, x_37);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_48 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
lean_inc(x_4);
x_52 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_4, x_11, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_44 = x_55;
goto block_47;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 1);
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
x_59 = lean_infer_type(x_41, x_9, x_10, x_11, x_12, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_mk_string_unchecked("", 0, 0);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
lean_inc(x_41);
x_64 = l_Lean_MessageData_ofExpr(x_41);
lean_inc(x_63);
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_64);
lean_ctor_set(x_52, 0, x_63);
x_65 = lean_mk_string_unchecked(" : ", 3, 3);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_66);
lean_ctor_set(x_15, 0, x_52);
x_67 = l_Lean_MessageData_ofExpr(x_60);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_15);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
x_70 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_4, x_69, x_9, x_10, x_11, x_12, x_61);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_44 = x_71;
goto block_47;
}
else
{
uint8_t x_72; 
lean_free_object(x_52);
lean_dec(x_43);
lean_dec(x_41);
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_59);
if (x_72 == 0)
{
return x_59;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_59, 0);
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_59);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_52, 1);
lean_inc(x_76);
lean_dec(x_52);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_41);
x_77 = lean_infer_type(x_41, x_9, x_10, x_11, x_12, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_mk_string_unchecked("", 0, 0);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
lean_inc(x_41);
x_82 = l_Lean_MessageData_ofExpr(x_41);
lean_inc(x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked(" : ", 3, 3);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_85);
lean_ctor_set(x_15, 0, x_83);
x_86 = l_Lean_MessageData_ofExpr(x_78);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_15);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_81);
x_89 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_4, x_88, x_9, x_10, x_11, x_12, x_79);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_44 = x_90;
goto block_47;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_43);
lean_dec(x_41);
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_91 = lean_ctor_get(x_77, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_77, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_93 = x_77;
} else {
 lean_dec_ref(x_77);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_43);
lean_dec(x_41);
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_48);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_48, 0);
lean_dec(x_96);
x_97 = lean_box(0);
lean_ctor_set(x_48, 0, x_97);
return x_48;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_48, 1);
lean_inc(x_98);
lean_dec(x_48);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_43);
lean_dec(x_41);
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_48);
if (x_101 == 0)
{
return x_48;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_48, 0);
x_103 = lean_ctor_get(x_48, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_48);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
block_47:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_41);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_105; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_35);
if (x_105 == 0)
{
return x_35;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_35, 0);
x_107 = lean_ctor_get(x_35, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_35);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_31);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_31, 0);
lean_dec(x_110);
x_111 = lean_ctor_get(x_33, 0);
lean_inc(x_111);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_111);
return x_31;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_31, 1);
lean_inc(x_112);
lean_dec(x_31);
x_113 = lean_ctor_get(x_33, 0);
lean_inc(x_113);
lean_dec(x_33);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_31);
if (x_115 == 0)
{
return x_31;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_31, 0);
x_117 = lean_ctor_get(x_31, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_31);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; size_t x_125; size_t x_126; lean_object* x_127; 
lean_dec(x_16);
x_119 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec(x_1);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_array_get_size(x_119);
x_122 = l_Array_toSubarray___redArg(x_119, x_120, x_121);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_array_size(x_19);
x_126 = lean_usize_of_nat(x_120);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_127 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0(x_19, x_125, x_126, x_124, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec(x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_131 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_144; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Meta_mkOfEqTrueCore(x_3, x_132);
x_135 = l_Lean_mkAppN(x_134, x_19);
lean_dec(x_19);
x_136 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_135, x_10, x_133);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_144 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_137, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_138);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
lean_inc(x_4);
x_148 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_4, x_11, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_unbox(x_149);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; 
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_140 = x_151;
goto block_143;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_153 = x_148;
} else {
 lean_dec_ref(x_148);
 x_153 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_137);
x_154 = lean_infer_type(x_137, x_9, x_10, x_11, x_12, x_152);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_mk_string_unchecked("", 0, 0);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
lean_inc(x_137);
x_159 = l_Lean_MessageData_ofExpr(x_137);
lean_inc(x_158);
if (lean_is_scalar(x_153)) {
 x_160 = lean_alloc_ctor(7, 2, 0);
} else {
 x_160 = x_153;
 lean_ctor_set_tag(x_160, 7);
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked(" : ", 3, 3);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_162);
lean_ctor_set(x_15, 0, x_160);
x_163 = l_Lean_MessageData_ofExpr(x_155);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_15);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_158);
x_166 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_4, x_165, x_9, x_10, x_11, x_12, x_156);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_140 = x_167;
goto block_143;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_153);
lean_dec(x_139);
lean_dec(x_137);
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_139);
lean_dec(x_137);
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_172 = lean_ctor_get(x_144, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_173 = x_144;
} else {
 lean_dec_ref(x_144);
 x_173 = lean_box(0);
}
x_174 = lean_box(0);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_139);
lean_dec(x_137);
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_176 = lean_ctor_get(x_144, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_144, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_178 = x_144;
} else {
 lean_dec_ref(x_144);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
block_143:
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_137);
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_139;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_180 = lean_ctor_get(x_131, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_131, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_182 = x_131;
} else {
 lean_dec_ref(x_131);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = lean_ctor_get(x_127, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_185 = x_127;
} else {
 lean_dec_ref(x_127);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_129, 0);
lean_inc(x_186);
lean_dec(x_129);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_185;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_184);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = lean_ctor_get(x_127, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_127, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_190 = x_127;
} else {
 lean_dec_ref(x_127);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; size_t x_200; size_t x_201; lean_object* x_202; 
x_192 = lean_ctor_get(x_15, 0);
lean_inc(x_192);
lean_dec(x_15);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_193 = x_16;
} else {
 lean_dec_ref(x_16);
 x_193 = lean_box(0);
}
x_194 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec(x_1);
x_195 = lean_unsigned_to_nat(0u);
x_196 = lean_array_get_size(x_194);
x_197 = l_Array_toSubarray___redArg(x_194, x_195, x_196);
x_198 = lean_box(0);
if (lean_is_scalar(x_193)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_193;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = lean_array_size(x_192);
x_201 = lean_usize_of_nat(x_195);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_202 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0(x_192, x_200, x_201, x_199, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_206 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_219; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = l_Lean_Meta_mkOfEqTrueCore(x_3, x_207);
x_210 = l_Lean_mkAppN(x_209, x_192);
lean_dec(x_192);
x_211 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_preprocess_spec__0___redArg(x_210, x_10, x_208);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_219 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_212, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_213);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_unbox(x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
lean_inc(x_4);
x_223 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_4, x_11, x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_215 = x_226;
goto block_218;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_228 = x_223;
} else {
 lean_dec_ref(x_223);
 x_228 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_212);
x_229 = lean_infer_type(x_212, x_9, x_10, x_11, x_12, x_227);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_mk_string_unchecked("", 0, 0);
x_233 = l_Lean_stringToMessageData(x_232);
lean_dec(x_232);
lean_inc(x_212);
x_234 = l_Lean_MessageData_ofExpr(x_212);
lean_inc(x_233);
if (lean_is_scalar(x_228)) {
 x_235 = lean_alloc_ctor(7, 2, 0);
} else {
 x_235 = x_228;
 lean_ctor_set_tag(x_235, 7);
}
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_mk_string_unchecked(" : ", 3, 3);
x_237 = l_Lean_stringToMessageData(x_236);
lean_dec(x_236);
x_238 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Lean_MessageData_ofExpr(x_230);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_233);
x_242 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_4, x_241, x_9, x_10, x_11, x_12, x_231);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_215 = x_243;
goto block_218;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_228);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_244 = lean_ctor_get(x_229, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_229, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_246 = x_229;
} else {
 lean_dec_ref(x_229);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_248 = lean_ctor_get(x_219, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_249 = x_219;
} else {
 lean_dec_ref(x_219);
 x_249 = lean_box(0);
}
x_250 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_252 = lean_ctor_get(x_219, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_219, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_254 = x_219;
} else {
 lean_dec_ref(x_219);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
block_218:
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_212);
if (lean_is_scalar(x_214)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_214;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_192);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_256 = lean_ctor_get(x_206, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_206, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_258 = x_206;
} else {
 lean_dec_ref(x_206);
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
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_192);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_260 = lean_ctor_get(x_202, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_261 = x_202;
} else {
 lean_dec_ref(x_202);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_204, 0);
lean_inc(x_262);
lean_dec(x_204);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_260);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_192);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_264 = lean_ctor_get(x_202, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_202, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_266 = x_202;
} else {
 lean_dec_ref(x_202);
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
uint8_t x_268; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_268 = !lean_is_exclusive(x_14);
if (x_268 == 0)
{
return x_14;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_14, 0);
x_270 = lean_ctor_get(x_14, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_14);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_15 = lean_mk_string_unchecked("grind", 5, 5);
x_16 = lean_mk_string_unchecked("debug", 5, 5);
x_17 = lean_mk_string_unchecked("matchCond", 9, 9);
x_18 = lean_mk_string_unchecked("proveFalse", 10, 10);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
lean_inc(x_19);
x_61 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_19, x_8, x_10);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_64;
goto block_60;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
x_68 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_68, 1);
x_71 = lean_ctor_get(x_68, 0);
lean_dec(x_71);
x_72 = lean_mk_string_unchecked("", 0, 0);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
lean_inc(x_1);
x_74 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_73);
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_74);
lean_ctor_set(x_68, 0, x_73);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_73);
lean_ctor_set(x_61, 0, x_68);
lean_inc(x_19);
x_75 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_19, x_61, x_6, x_7, x_8, x_9, x_70);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_76;
goto block_60;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_dec(x_68);
x_78 = lean_mk_string_unchecked("", 0, 0);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
lean_inc(x_1);
x_80 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_79);
lean_ctor_set(x_61, 0, x_81);
lean_inc(x_19);
x_82 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_19, x_61, x_6, x_7, x_8, x_9, x_77);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_83;
goto block_60;
}
}
else
{
lean_free_object(x_61);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_68;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_61, 1);
lean_inc(x_84);
lean_dec(x_61);
x_85 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
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
x_88 = lean_mk_string_unchecked("", 0, 0);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
lean_inc(x_1);
x_90 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_89);
if (lean_is_scalar(x_87)) {
 x_91 = lean_alloc_ctor(7, 2, 0);
} else {
 x_91 = x_87;
 lean_ctor_set_tag(x_91, 7);
}
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
lean_inc(x_19);
x_93 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_19, x_92, x_6, x_7, x_8, x_9, x_86);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = x_94;
goto block_60;
}
else
{
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_85;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_60:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_inc(x_1);
x_29 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_25, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_cleanupAnnotations(x_30);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_11 = x_31;
goto block_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc(x_32);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = lean_mk_string_unchecked("Lean", 4, 4);
x_36 = lean_mk_string_unchecked("Grind", 5, 5);
x_37 = lean_mk_string_unchecked("MatchCond", 9, 9);
x_38 = l_Lean_Name_mkStr3(x_35, x_36, x_37);
x_39 = l_Lean_Expr_isConstOf(x_34, x_38);
lean_dec(x_38);
lean_dec(x_34);
if (x_39 == 0)
{
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_11 = x_31;
goto block_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_box(0);
x_42 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed), 13, 4);
lean_closure_set(x_42, 0, x_40);
lean_closure_set(x_42, 1, x_41);
lean_closure_set(x_42, 2, x_1);
lean_closure_set(x_42, 3, x_19);
x_43 = lean_box(0);
x_44 = lean_unbox(x_43);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_45 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg(x_42, x_44, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_31);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
x_55 = l_Lean_Meta_Grind_closeGoal(x_54, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_53);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
return x_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
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
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_tryToProveFalse_spec__0(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssignable___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_hasAssignableLevelMVar___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_anyM___at___Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___lam__0(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_hasAssignableMVar___at___Lean_Meta_Grind_tryToProveFalse_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_Grind_tryToProveFalse_spec__8(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Meta_Grind_tryToProveFalse___lam__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_28 = lean_mk_string_unchecked("grind", 5, 5);
x_29 = lean_mk_string_unchecked("debug", 5, 5);
x_30 = lean_mk_string_unchecked("matchCond", 9, 9);
x_31 = l_Lean_Name_mkStr3(x_28, x_29, x_30);
lean_inc(x_31);
x_169 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_31, x_8, x_10);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_172;
goto block_168;
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_169);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_169, 1);
x_175 = lean_ctor_get(x_169, 0);
lean_dec(x_175);
x_176 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_174);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_176, 1);
x_179 = lean_ctor_get(x_176, 0);
lean_dec(x_179);
x_180 = lean_mk_string_unchecked("visiting", 8, 8);
x_181 = l_Lean_stringToMessageData(x_180);
lean_dec(x_180);
lean_inc(x_1);
x_182 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_176, 7);
lean_ctor_set(x_176, 1, x_182);
lean_ctor_set(x_176, 0, x_181);
x_183 = lean_mk_string_unchecked("", 0, 0);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
lean_ctor_set_tag(x_169, 7);
lean_ctor_set(x_169, 1, x_184);
lean_ctor_set(x_169, 0, x_176);
lean_inc(x_31);
x_185 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_31, x_169, x_6, x_7, x_8, x_9, x_178);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_186;
goto block_168;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_187 = lean_ctor_get(x_176, 1);
lean_inc(x_187);
lean_dec(x_176);
x_188 = lean_mk_string_unchecked("visiting", 8, 8);
x_189 = l_Lean_stringToMessageData(x_188);
lean_dec(x_188);
lean_inc(x_1);
x_190 = l_Lean_indentExpr(x_1);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_mk_string_unchecked("", 0, 0);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
lean_ctor_set_tag(x_169, 7);
lean_ctor_set(x_169, 1, x_193);
lean_ctor_set(x_169, 0, x_191);
lean_inc(x_31);
x_194 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_31, x_169, x_6, x_7, x_8, x_9, x_187);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_195;
goto block_168;
}
}
else
{
lean_free_object(x_169);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_176;
}
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_169, 1);
lean_inc(x_196);
lean_dec(x_169);
x_197 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_mk_string_unchecked("visiting", 8, 8);
x_201 = l_Lean_stringToMessageData(x_200);
lean_dec(x_200);
lean_inc(x_1);
x_202 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_199)) {
 x_203 = lean_alloc_ctor(7, 2, 0);
} else {
 x_203 = x_199;
 lean_ctor_set_tag(x_203, 7);
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_mk_string_unchecked("", 0, 0);
x_205 = l_Lean_stringToMessageData(x_204);
lean_dec(x_204);
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_205);
lean_inc(x_31);
x_207 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_31, x_206, x_6, x_7, x_8, x_9, x_198);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_208;
goto block_168;
}
else
{
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_197;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
lean_inc(x_1);
x_25 = l_Lean_Meta_mkEqTrueCore(x_1, x_15);
x_26 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_25, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_26;
}
block_168:
{
lean_object* x_41; 
lean_inc(x_1);
x_41 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_32, x_35, x_38, x_39, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_1);
x_45 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied(x_1, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_1);
x_55 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(x_1, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_32);
lean_dec(x_31);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_Grind_getConfig___redArg(x_34, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_59, sizeof(void*)*7 + 10);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_11 = x_61;
goto block_14;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_58, 1);
x_64 = lean_ctor_get(x_58, 0);
lean_dec(x_64);
x_65 = lean_mk_string_unchecked("failed to construct proof for", 29, 29);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_58, 7);
lean_ctor_set(x_58, 1, x_67);
lean_ctor_set(x_58, 0, x_66);
x_68 = lean_mk_string_unchecked("", 0, 0);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Meta_Grind_reportIssue(x_70, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_63);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_11 = x_72;
goto block_14;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_58, 1);
lean_inc(x_73);
lean_dec(x_58);
x_74 = lean_mk_string_unchecked("failed to construct proof for", 29, 29);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = l_Lean_indentExpr(x_1);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked("", 0, 0);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Meta_Grind_reportIssue(x_80, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_73);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_11 = x_82;
goto block_14;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_55, 1);
lean_inc(x_83);
lean_dec(x_55);
x_84 = lean_ctor_get(x_56, 0);
lean_inc(x_84);
lean_dec(x_56);
lean_inc(x_31);
x_85 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_31, x_38, x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_31);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_15 = x_84;
x_16 = x_32;
x_17 = x_33;
x_18 = x_34;
x_19 = x_35;
x_20 = x_36;
x_21 = x_37;
x_22 = x_38;
x_23 = x_39;
x_24 = x_88;
goto block_27;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 1);
x_91 = lean_ctor_get(x_85, 0);
lean_dec(x_91);
x_92 = l_Lean_Meta_Grind_updateLastTag(x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_90);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_92, 1);
x_95 = lean_ctor_get(x_92, 0);
lean_dec(x_95);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_84);
x_96 = lean_infer_type(x_84, x_36, x_37, x_38, x_39, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_mk_string_unchecked("", 0, 0);
x_100 = l_Lean_stringToMessageData(x_99);
lean_dec(x_99);
x_101 = l_Lean_MessageData_ofExpr(x_97);
lean_inc(x_100);
lean_ctor_set_tag(x_92, 7);
lean_ctor_set(x_92, 1, x_101);
lean_ctor_set(x_92, 0, x_100);
lean_ctor_set_tag(x_85, 7);
lean_ctor_set(x_85, 1, x_100);
lean_ctor_set(x_85, 0, x_92);
x_102 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_31, x_85, x_36, x_37, x_38, x_39, x_98);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_15 = x_84;
x_16 = x_32;
x_17 = x_33;
x_18 = x_34;
x_19 = x_35;
x_20 = x_36;
x_21 = x_37;
x_22 = x_38;
x_23 = x_39;
x_24 = x_103;
goto block_27;
}
else
{
uint8_t x_104; 
lean_free_object(x_92);
lean_free_object(x_85);
lean_dec(x_84);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_96);
if (x_104 == 0)
{
return x_96;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_96, 0);
x_106 = lean_ctor_get(x_96, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_96);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_92, 1);
lean_inc(x_108);
lean_dec(x_92);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_84);
x_109 = lean_infer_type(x_84, x_36, x_37, x_38, x_39, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_mk_string_unchecked("", 0, 0);
x_113 = l_Lean_stringToMessageData(x_112);
lean_dec(x_112);
x_114 = l_Lean_MessageData_ofExpr(x_110);
lean_inc(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_tag(x_85, 7);
lean_ctor_set(x_85, 1, x_113);
lean_ctor_set(x_85, 0, x_115);
x_116 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_31, x_85, x_36, x_37, x_38, x_39, x_111);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_15 = x_84;
x_16 = x_32;
x_17 = x_33;
x_18 = x_34;
x_19 = x_35;
x_20 = x_36;
x_21 = x_37;
x_22 = x_38;
x_23 = x_39;
x_24 = x_117;
goto block_27;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_free_object(x_85);
lean_dec(x_84);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_118 = lean_ctor_get(x_109, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_109, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_120 = x_109;
} else {
 lean_dec_ref(x_109);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_free_object(x_85);
lean_dec(x_84);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
return x_92;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_85, 1);
lean_inc(x_122);
lean_dec(x_85);
x_123 = l_Lean_Meta_Grind_updateLastTag(x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_84);
x_126 = lean_infer_type(x_84, x_36, x_37, x_38, x_39, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_mk_string_unchecked("", 0, 0);
x_130 = l_Lean_stringToMessageData(x_129);
lean_dec(x_129);
x_131 = l_Lean_MessageData_ofExpr(x_127);
lean_inc(x_130);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(7, 2, 0);
} else {
 x_132 = x_125;
 lean_ctor_set_tag(x_132, 7);
}
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
x_134 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_31, x_133, x_36, x_37, x_38, x_39, x_128);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_15 = x_84;
x_16 = x_32;
x_17 = x_33;
x_18 = x_34;
x_19 = x_35;
x_20 = x_36;
x_21 = x_37;
x_22 = x_38;
x_23 = x_39;
x_24 = x_135;
goto block_27;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_125);
lean_dec(x_84);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_136 = lean_ctor_get(x_126, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_126, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_138 = x_126;
} else {
 lean_dec_ref(x_126);
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
lean_dec(x_84);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
return x_123;
}
}
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_55);
if (x_140 == 0)
{
return x_55;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_55, 0);
x_142 = lean_ctor_get(x_55, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_55);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_45);
if (x_144 == 0)
{
return x_45;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_45, 0);
x_146 = lean_ctor_get(x_45, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_45);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_31);
x_148 = lean_ctor_get(x_41, 1);
lean_inc(x_148);
lean_dec(x_41);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_1);
x_149 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied(x_1, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = l_Lean_Meta_Grind_tryToProveFalse(x_1, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_152);
return x_153;
}
else
{
uint8_t x_154; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_149);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_149, 0);
lean_dec(x_155);
x_156 = lean_box(0);
lean_ctor_set(x_149, 0, x_156);
return x_149;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_149, 1);
lean_inc(x_157);
lean_dec(x_149);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_149);
if (x_160 == 0)
{
return x_149;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_149, 0);
x_162 = lean_ctor_get(x_149, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_149);
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
uint8_t x_164; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_41);
if (x_164 == 0)
{
return x_41;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_41, 0);
x_166 = lean_ctor_get(x_41, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_41);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1____x40_Lean_Meta_Tactic_Grind_MatchCond___hyg_11153_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("MatchCond", 9, 9);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp), 10, 0);
x_7 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isStatisfied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Meta_Grind_tryToProveFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
return x_21;
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
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1____x40_Lean_Meta_Tactic_Grind_MatchCond___hyg_11235_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("MatchCond", 9, 9);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown), 10, 0);
x_7 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_5, x_6, x_1);
return x_7;
}
}
lean_object* initialize_Init_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1____x40_Lean_Meta_Tactic_Grind_MatchCond___hyg_11153_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1____x40_Lean_Meta_Tactic_Grind_MatchCond___hyg_11235_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
