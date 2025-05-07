// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrite
// Imports: Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Replace Lean.Elab.Tactic.Location Lean.Elab.Tactic.Config
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1350____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__2___boxed(lean_object**);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoTreeContext___at___Lean_Elab_Tactic_evalTactic_eval_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_hasSyntheticSorry(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Tactic_getMainGoal(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Tactic_getMainTarget(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_25 = l_Lean_MVarId_rewrite(x_20, x_23, x_16, x_4, x_5, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Tactic_getMainGoal(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_33 = l_Lean_MVarId_replaceTargetEq(x_29, x_31, x_32, x_10, x_11, x_12, x_13, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_26, 2);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_37, x_7, x_10, x_11, x_12, x_13, x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
return x_25;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_25, 0);
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_25);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
return x_19;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(x_17);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_box(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed), 14, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_3);
x_17 = lean_box(1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
x_19 = lean_unbox(x_17);
x_20 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Elab_Tactic_rewriteTarget___lam__0(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_rewriteTarget(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_hasSyntheticSorry(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_11);
x_20 = l_Lean_FVarId_getDecl___redArg(x_4, x_11, x_13, x_14, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Tactic_getMainGoal(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_MVarId_rewrite(x_24, x_26, x_17, x_5, x_6, x_11, x_12, x_13, x_14, x_25);
lean_dec(x_11);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_17);
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
x_36 = l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(x_18);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
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
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___boxed), 11, 4);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_13, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_22 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_18, x_3, x_20, x_21, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_15, 2);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_27, x_5, x_8, x_9, x_10, x_11, x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(0);
x_15 = lean_box(1);
x_16 = lean_box(x_2);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed), 15, 6);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_4);
x_18 = lean_box(1);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed), 12, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_3);
x_20 = l_Lean_Elab_Tactic_withMainContext___redArg(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(x_1, x_2, x_16, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_Tactic_rewriteLocalDecl(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_16 = lean_mk_string_unchecked("failed to rewrite using equation theorems for '", 47, 47);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = l_Lean_MessageData_ofName(x_4);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("'.", 2, 2);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
x_24 = lean_mk_string_unchecked("", 0, 0);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_26, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = l_Lean_Elab_Tactic_saveState___redArg(x_8, x_10, x_12, x_13, x_14, x_15);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_mkCIdentFrom(x_3, x_28, x_34);
x_36 = lean_box(x_2);
lean_inc(x_1);
x_37 = lean_apply_2(x_1, x_36, x_35);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_38 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_46 = l_Lean_Exception_isInterrupt(x_39);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Exception_isRuntime(x_39);
lean_dec(x_39);
x_41 = x_47;
goto block_45;
}
else
{
lean_dec(x_39);
x_41 = x_46;
goto block_45;
}
block_45:
{
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
x_42 = l_Lean_Elab_Tactic_SavedState_restore(x_31, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_6 = x_29;
x_15 = x_43;
goto _start;
}
else
{
lean_dec(x_40);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getFVarId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_55; lean_object* x_159; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = l_Lean_Elab_Tactic_saveState___redArg(x_8, x_10, x_12, x_13, x_14, x_15);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_6);
x_173 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_173, 0, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_174 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_173, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_dec(x_171);
x_159 = x_174;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_181; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
x_181 = l_Lean_Exception_isInterrupt(x_175);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = l_Lean_Exception_isRuntime(x_175);
lean_dec(x_175);
x_177 = x_182;
goto block_180;
}
else
{
lean_dec(x_175);
x_177 = x_181;
goto block_180;
}
block_180:
{
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_174);
x_178 = l_Lean_Elab_Tactic_SavedState_restore(x_171, x_177, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_176);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_55 = x_179;
goto block_158;
}
else
{
lean_dec(x_176);
lean_dec(x_171);
x_159 = x_174;
goto block_169;
}
}
}
block_44:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_to_list(x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_16);
x_22 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_6, x_16, x_20, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
lean_dec(x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_16, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_11, 2);
lean_inc(x_27);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Term_addTermInfo(x_6, x_25, x_28, x_29, x_30, x_17, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_4);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_4);
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
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_22;
}
}
block_54:
{
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_46);
x_49 = l_Lean_Elab_Tactic_SavedState_restore(x_45, x_48, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_47);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(x_2);
x_52 = lean_apply_11(x_1, x_51, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_50);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
block_158:
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Elab_Tactic_saveState___redArg(x_8, x_10, x_12, x_13, x_14, x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
x_60 = l_Lean_realizeGlobalConstNoOverload(x_6, x_13, x_14, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_62);
x_64 = l_Lean_Meta_getEqnsFor_x3f(x_62, x_11, x_12, x_13, x_14, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_60);
lean_dec(x_62);
lean_free_object(x_56);
lean_dec(x_6);
lean_dec(x_4);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(x_2);
x_68 = lean_apply_11(x_1, x_67, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_3);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_box(0);
x_72 = lean_array_get_size(x_70);
x_73 = lean_nat_dec_eq(x_72, x_5);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_mk_string_unchecked(" Try rewriting with '", 21, 21);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_62);
x_77 = l_Lean_Name_str___override(x_62, x_76);
x_78 = l_Lean_MessageData_ofName(x_77);
lean_ctor_set_tag(x_60, 7);
lean_ctor_set(x_60, 1, x_78);
lean_ctor_set(x_60, 0, x_75);
x_79 = lean_mk_string_unchecked("'.", 2, 2);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_80);
lean_ctor_set(x_56, 0, x_60);
x_81 = lean_unbox(x_71);
x_16 = x_62;
x_17 = x_81;
x_18 = x_69;
x_19 = x_70;
x_20 = x_56;
goto block_44;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_free_object(x_60);
lean_free_object(x_56);
x_82 = lean_mk_string_unchecked("", 0, 0);
x_83 = l_Lean_stringToMessageData(x_82);
lean_dec(x_82);
x_84 = lean_unbox(x_71);
x_16 = x_62;
x_17 = x_84;
x_18 = x_69;
x_19 = x_70;
x_20 = x_83;
goto block_44;
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_60);
lean_dec(x_62);
lean_free_object(x_56);
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
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_64);
if (x_85 == 0)
{
return x_64;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_64, 0);
x_87 = lean_ctor_get(x_64, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_64);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_60, 0);
x_90 = lean_ctor_get(x_60, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_60);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_89);
x_91 = l_Lean_Meta_getEqnsFor_x3f(x_89, x_11, x_12, x_13, x_14, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_89);
lean_free_object(x_56);
lean_dec(x_6);
lean_dec(x_4);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_box(x_2);
x_95 = lean_apply_11(x_1, x_94, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_3);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_box(0);
x_99 = lean_array_get_size(x_97);
x_100 = lean_nat_dec_eq(x_99, x_5);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_101 = lean_mk_string_unchecked(" Try rewriting with '", 21, 21);
x_102 = l_Lean_stringToMessageData(x_101);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_89);
x_104 = l_Lean_Name_str___override(x_89, x_103);
x_105 = l_Lean_MessageData_ofName(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("'.", 2, 2);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_108);
lean_ctor_set(x_56, 0, x_106);
x_109 = lean_unbox(x_98);
x_16 = x_89;
x_17 = x_109;
x_18 = x_96;
x_19 = x_97;
x_20 = x_56;
goto block_44;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_free_object(x_56);
x_110 = lean_mk_string_unchecked("", 0, 0);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
x_112 = lean_unbox(x_98);
x_16 = x_89;
x_17 = x_112;
x_18 = x_96;
x_19 = x_97;
x_20 = x_111;
goto block_44;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_89);
lean_free_object(x_56);
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
lean_dec(x_1);
x_113 = lean_ctor_get(x_91, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_91, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_115 = x_91;
} else {
 lean_dec_ref(x_91);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_free_object(x_56);
lean_dec(x_6);
lean_dec(x_4);
x_117 = lean_ctor_get(x_60, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_60, 1);
lean_inc(x_118);
lean_dec(x_60);
x_119 = l_Lean_Exception_isInterrupt(x_117);
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = l_Lean_Exception_isRuntime(x_117);
x_45 = x_58;
x_46 = x_117;
x_47 = x_118;
x_48 = x_120;
goto block_54;
}
else
{
x_45 = x_58;
x_46 = x_117;
x_47 = x_118;
x_48 = x_119;
goto block_54;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_56, 0);
x_122 = lean_ctor_get(x_56, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_56);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
x_123 = l_Lean_realizeGlobalConstNoOverload(x_6, x_13, x_14, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_124);
x_127 = l_Lean_Meta_getEqnsFor_x3f(x_124, x_11, x_12, x_13, x_14, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_6);
lean_dec(x_4);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_box(x_2);
x_131 = lean_apply_11(x_1, x_130, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_129);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_3);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
lean_dec(x_128);
x_134 = lean_box(0);
x_135 = lean_array_get_size(x_133);
x_136 = lean_nat_dec_eq(x_135, x_5);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_137 = lean_mk_string_unchecked(" Try rewriting with '", 21, 21);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
x_139 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_124);
x_140 = l_Lean_Name_str___override(x_124, x_139);
x_141 = l_Lean_MessageData_ofName(x_140);
if (lean_is_scalar(x_126)) {
 x_142 = lean_alloc_ctor(7, 2, 0);
} else {
 x_142 = x_126;
 lean_ctor_set_tag(x_142, 7);
}
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked("'.", 2, 2);
x_144 = l_Lean_stringToMessageData(x_143);
lean_dec(x_143);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_unbox(x_134);
x_16 = x_124;
x_17 = x_146;
x_18 = x_132;
x_19 = x_133;
x_20 = x_145;
goto block_44;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_126);
x_147 = lean_mk_string_unchecked("", 0, 0);
x_148 = l_Lean_stringToMessageData(x_147);
lean_dec(x_147);
x_149 = lean_unbox(x_134);
x_16 = x_124;
x_17 = x_149;
x_18 = x_132;
x_19 = x_133;
x_20 = x_148;
goto block_44;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_126);
lean_dec(x_124);
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
lean_dec(x_1);
x_150 = lean_ctor_get(x_127, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_127, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_152 = x_127;
} else {
 lean_dec_ref(x_127);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_6);
lean_dec(x_4);
x_154 = lean_ctor_get(x_123, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_123, 1);
lean_inc(x_155);
lean_dec(x_123);
x_156 = l_Lean_Exception_isInterrupt(x_154);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = l_Lean_Exception_isRuntime(x_154);
x_45 = x_121;
x_46 = x_154;
x_47 = x_155;
x_48 = x_157;
goto block_54;
}
else
{
x_45 = x_121;
x_46 = x_154;
x_47 = x_155;
x_48 = x_156;
goto block_54;
}
}
}
}
block_169:
{
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_55 = x_161;
goto block_158;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_160);
lean_dec(x_6);
lean_dec(x_4);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_box(x_2);
x_164 = lean_apply_11(x_1, x_163, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_162);
return x_164;
}
}
else
{
uint8_t x_165; 
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
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_159);
if (x_165 == 0)
{
return x_159;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_159, 0);
x_167 = lean_ctor_get(x_159, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_159);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_15, 5);
x_19 = l_Lean_replaceRef(x_1, x_18);
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_15, 2);
x_23 = lean_ctor_get(x_15, 3);
x_24 = lean_ctor_get(x_15, 4);
x_25 = lean_ctor_get(x_15, 6);
x_26 = lean_ctor_get(x_15, 7);
x_27 = lean_ctor_get(x_15, 8);
x_28 = lean_ctor_get(x_15, 9);
x_29 = lean_ctor_get(x_15, 10);
x_30 = lean_ctor_get_uint8(x_15, sizeof(void*)*13);
x_31 = lean_ctor_get(x_15, 11);
x_32 = lean_ctor_get_uint8(x_15, sizeof(void*)*13 + 1);
x_33 = lean_ctor_get(x_15, 12);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_34 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_21);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_23);
lean_ctor_set(x_34, 4, x_24);
lean_ctor_set(x_34, 5, x_19);
lean_ctor_set(x_34, 6, x_25);
lean_ctor_set(x_34, 7, x_26);
lean_ctor_set(x_34, 8, x_27);
lean_ctor_set(x_34, 9, x_28);
lean_ctor_set(x_34, 10, x_29);
lean_ctor_set(x_34, 11, x_31);
lean_ctor_set(x_34, 12, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*13, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*13 + 1, x_32);
if (x_2 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_mk_string_unchecked("Lean", 4, 4);
x_36 = lean_mk_string_unchecked("Parser", 6, 6);
x_37 = lean_mk_string_unchecked("Term", 4, 4);
x_38 = lean_mk_string_unchecked("explicit", 8, 8);
x_39 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_38);
lean_inc(x_3);
x_40 = l_Lean_Syntax_isOfKind(x_3, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
x_41 = lean_box(x_5);
x_42 = lean_apply_11(x_4, x_41, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_34, x_16, x_17);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Syntax_getArg(x_3, x_6);
lean_inc(x_43);
x_44 = l_Lean_Syntax_isOfKind(x_43, x_7);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_8);
x_45 = lean_box(x_5);
x_46 = lean_apply_11(x_4, x_45, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_34, x_16, x_17);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_apply_10(x_8, x_43, x_9, x_10, x_11, x_12, x_13, x_14, x_34, x_16, x_17);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_4);
x_48 = lean_apply_10(x_8, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_34, x_16, x_17);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
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
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_nat_dec_lt(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_47; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_instInhabitedSyntax;
x_21 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_shiftl(x_5, x_18);
x_25 = lean_array_get(x_20, x_21, x_24);
x_61 = lean_nat_add(x_24, x_18);
lean_dec(x_24);
x_62 = lean_array_get_size(x_21);
x_63 = lean_nat_dec_lt(x_61, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_21);
x_64 = lean_box(0);
x_47 = x_64;
goto block_60;
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget(x_21, x_61);
lean_dec(x_61);
lean_dec(x_21);
x_47 = x_65;
goto block_60;
}
block_46:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_mk_string_unchecked("ident", 5, 5);
x_29 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Syntax_getArg(x_25, x_18);
x_33 = lean_box(x_27);
lean_inc(x_32);
lean_inc(x_2);
x_34 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__1___boxed), 15, 5);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_32);
lean_closure_set(x_34, 3, x_22);
lean_closure_set(x_34, 4, x_18);
x_35 = l_Lean_Name_mkStr1(x_28);
lean_inc(x_32);
x_36 = l_Lean_Syntax_isOfKind(x_32, x_35);
x_37 = lean_box(x_36);
x_38 = lean_box(x_27);
lean_inc(x_2);
x_39 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__2___boxed), 17, 8);
lean_closure_set(x_39, 0, x_25);
lean_closure_set(x_39, 1, x_37);
lean_closure_set(x_39, 2, x_32);
lean_closure_set(x_39, 3, x_2);
lean_closure_set(x_39, 4, x_38);
lean_closure_set(x_39, 5, x_18);
lean_closure_set(x_39, 6, x_35);
lean_closure_set(x_39, 7, x_34);
x_40 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__3), 11, 1);
lean_closure_set(x_40, 0, x_30);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Elab_withInfoTreeContext___at___Lean_Elab_Tactic_evalTactic_eval_spec__5(lean_box(0), x_39, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_3, 2);
x_44 = lean_nat_add(x_5, x_43);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_44;
x_14 = x_42;
goto _start;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_41;
}
}
block_60:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_mk_empty_array_with_capacity(x_48);
lean_inc(x_25);
x_50 = lean_array_push(x_49, x_25);
x_51 = lean_array_push(x_50, x_47);
x_52 = lean_mk_string_unchecked("null", 4, 4);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_box(2);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_51);
x_56 = l_Lean_Syntax_getArg(x_25, x_23);
x_57 = l_Lean_Syntax_isNone(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
x_26 = x_55;
x_27 = x_16;
goto block_46;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_box(0);
x_59 = lean_unbox(x_58);
x_26 = x_55;
x_27 = x_59;
goto block_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_55; lean_object* x_159; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = l_Lean_Elab_Tactic_saveState___redArg(x_8, x_10, x_12, x_13, x_14, x_15);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_6);
x_173 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_173, 0, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_174 = l_Lean_Elab_Tactic_withoutRecover(lean_box(0), x_173, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_dec(x_171);
x_159 = x_174;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_181; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
x_181 = l_Lean_Exception_isInterrupt(x_175);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = l_Lean_Exception_isRuntime(x_175);
lean_dec(x_175);
x_177 = x_182;
goto block_180;
}
else
{
lean_dec(x_175);
x_177 = x_181;
goto block_180;
}
block_180:
{
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_174);
x_178 = l_Lean_Elab_Tactic_SavedState_restore(x_171, x_177, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_176);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_55 = x_179;
goto block_158;
}
else
{
lean_dec(x_176);
lean_dec(x_171);
x_159 = x_174;
goto block_169;
}
}
}
block_44:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_to_list(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
x_22 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_6, x_18, x_20, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
lean_dec(x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_18, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_11, 2);
lean_inc(x_27);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Term_addTermInfo(x_6, x_25, x_28, x_29, x_30, x_19, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_4);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_4);
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
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_22;
}
}
block_54:
{
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_47);
x_49 = l_Lean_Elab_Tactic_SavedState_restore(x_45, x_48, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(x_2);
x_52 = lean_apply_11(x_1, x_51, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_50);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
block_158:
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Elab_Tactic_saveState___redArg(x_8, x_10, x_12, x_13, x_14, x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
x_60 = l_Lean_realizeGlobalConstNoOverload(x_6, x_13, x_14, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_62);
x_64 = l_Lean_Meta_getEqnsFor_x3f(x_62, x_11, x_12, x_13, x_14, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_60);
lean_dec(x_62);
lean_free_object(x_56);
lean_dec(x_6);
lean_dec(x_4);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(x_2);
x_68 = lean_apply_11(x_1, x_67, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_3);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_box(0);
x_72 = lean_array_get_size(x_70);
x_73 = lean_nat_dec_eq(x_72, x_5);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_mk_string_unchecked(" Try rewriting with '", 21, 21);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_62);
x_77 = l_Lean_Name_str___override(x_62, x_76);
x_78 = l_Lean_MessageData_ofName(x_77);
lean_ctor_set_tag(x_60, 7);
lean_ctor_set(x_60, 1, x_78);
lean_ctor_set(x_60, 0, x_75);
x_79 = lean_mk_string_unchecked("'.", 2, 2);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_80);
lean_ctor_set(x_56, 0, x_60);
x_81 = lean_unbox(x_71);
x_16 = x_70;
x_17 = x_69;
x_18 = x_62;
x_19 = x_81;
x_20 = x_56;
goto block_44;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_free_object(x_60);
lean_free_object(x_56);
x_82 = lean_mk_string_unchecked("", 0, 0);
x_83 = l_Lean_stringToMessageData(x_82);
lean_dec(x_82);
x_84 = lean_unbox(x_71);
x_16 = x_70;
x_17 = x_69;
x_18 = x_62;
x_19 = x_84;
x_20 = x_83;
goto block_44;
}
}
}
else
{
uint8_t x_85; 
lean_free_object(x_60);
lean_dec(x_62);
lean_free_object(x_56);
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
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_64);
if (x_85 == 0)
{
return x_64;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_64, 0);
x_87 = lean_ctor_get(x_64, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_64);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_60, 0);
x_90 = lean_ctor_get(x_60, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_60);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_89);
x_91 = l_Lean_Meta_getEqnsFor_x3f(x_89, x_11, x_12, x_13, x_14, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_89);
lean_free_object(x_56);
lean_dec(x_6);
lean_dec(x_4);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_box(x_2);
x_95 = lean_apply_11(x_1, x_94, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_3);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_box(0);
x_99 = lean_array_get_size(x_97);
x_100 = lean_nat_dec_eq(x_99, x_5);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_101 = lean_mk_string_unchecked(" Try rewriting with '", 21, 21);
x_102 = l_Lean_stringToMessageData(x_101);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_89);
x_104 = l_Lean_Name_str___override(x_89, x_103);
x_105 = l_Lean_MessageData_ofName(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("'.", 2, 2);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_108);
lean_ctor_set(x_56, 0, x_106);
x_109 = lean_unbox(x_98);
x_16 = x_97;
x_17 = x_96;
x_18 = x_89;
x_19 = x_109;
x_20 = x_56;
goto block_44;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_free_object(x_56);
x_110 = lean_mk_string_unchecked("", 0, 0);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
x_112 = lean_unbox(x_98);
x_16 = x_97;
x_17 = x_96;
x_18 = x_89;
x_19 = x_112;
x_20 = x_111;
goto block_44;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_89);
lean_free_object(x_56);
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
lean_dec(x_1);
x_113 = lean_ctor_get(x_91, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_91, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_115 = x_91;
} else {
 lean_dec_ref(x_91);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_free_object(x_56);
lean_dec(x_6);
lean_dec(x_4);
x_117 = lean_ctor_get(x_60, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_60, 1);
lean_inc(x_118);
lean_dec(x_60);
x_119 = l_Lean_Exception_isInterrupt(x_117);
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = l_Lean_Exception_isRuntime(x_117);
x_45 = x_58;
x_46 = x_118;
x_47 = x_117;
x_48 = x_120;
goto block_54;
}
else
{
x_45 = x_58;
x_46 = x_118;
x_47 = x_117;
x_48 = x_119;
goto block_54;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_56, 0);
x_122 = lean_ctor_get(x_56, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_56);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
x_123 = l_Lean_realizeGlobalConstNoOverload(x_6, x_13, x_14, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_124);
x_127 = l_Lean_Meta_getEqnsFor_x3f(x_124, x_11, x_12, x_13, x_14, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_6);
lean_dec(x_4);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_box(x_2);
x_131 = lean_apply_11(x_1, x_130, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_129);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_3);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
lean_dec(x_128);
x_134 = lean_box(0);
x_135 = lean_array_get_size(x_133);
x_136 = lean_nat_dec_eq(x_135, x_5);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_137 = lean_mk_string_unchecked(" Try rewriting with '", 21, 21);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
x_139 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_124);
x_140 = l_Lean_Name_str___override(x_124, x_139);
x_141 = l_Lean_MessageData_ofName(x_140);
if (lean_is_scalar(x_126)) {
 x_142 = lean_alloc_ctor(7, 2, 0);
} else {
 x_142 = x_126;
 lean_ctor_set_tag(x_142, 7);
}
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked("'.", 2, 2);
x_144 = l_Lean_stringToMessageData(x_143);
lean_dec(x_143);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_unbox(x_134);
x_16 = x_133;
x_17 = x_132;
x_18 = x_124;
x_19 = x_146;
x_20 = x_145;
goto block_44;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_126);
x_147 = lean_mk_string_unchecked("", 0, 0);
x_148 = l_Lean_stringToMessageData(x_147);
lean_dec(x_147);
x_149 = lean_unbox(x_134);
x_16 = x_133;
x_17 = x_132;
x_18 = x_124;
x_19 = x_149;
x_20 = x_148;
goto block_44;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_126);
lean_dec(x_124);
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
lean_dec(x_1);
x_150 = lean_ctor_get(x_127, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_127, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_152 = x_127;
} else {
 lean_dec_ref(x_127);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_6);
lean_dec(x_4);
x_154 = lean_ctor_get(x_123, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_123, 1);
lean_inc(x_155);
lean_dec(x_123);
x_156 = l_Lean_Exception_isInterrupt(x_154);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = l_Lean_Exception_isRuntime(x_154);
x_45 = x_121;
x_46 = x_155;
x_47 = x_154;
x_48 = x_157;
goto block_54;
}
else
{
x_45 = x_121;
x_46 = x_155;
x_47 = x_154;
x_48 = x_156;
goto block_54;
}
}
}
}
block_169:
{
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_55 = x_161;
goto block_158;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_160);
lean_dec(x_6);
lean_dec(x_4);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_box(x_2);
x_164 = lean_apply_11(x_1, x_163, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_162);
return x_164;
}
}
else
{
uint8_t x_165; 
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
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_159);
if (x_165 == 0)
{
return x_159;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_159, 0);
x_167 = lean_ctor_get(x_159, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_159);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_nat_dec_lt(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_47; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_instInhabitedSyntax;
x_21 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_shiftl(x_5, x_18);
x_25 = lean_array_get(x_20, x_21, x_24);
x_61 = lean_nat_add(x_24, x_18);
lean_dec(x_24);
x_62 = lean_array_get_size(x_21);
x_63 = lean_nat_dec_lt(x_61, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_21);
x_64 = lean_box(0);
x_47 = x_64;
goto block_60;
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget(x_21, x_61);
lean_dec(x_61);
lean_dec(x_21);
x_47 = x_65;
goto block_60;
}
block_46:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_mk_string_unchecked("ident", 5, 5);
x_29 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Syntax_getArg(x_25, x_18);
x_33 = lean_box(x_27);
lean_inc(x_32);
lean_inc(x_2);
x_34 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__1___boxed), 15, 5);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_32);
lean_closure_set(x_34, 3, x_22);
lean_closure_set(x_34, 4, x_18);
x_35 = l_Lean_Name_mkStr1(x_28);
lean_inc(x_32);
x_36 = l_Lean_Syntax_isOfKind(x_32, x_35);
x_37 = lean_box(x_36);
x_38 = lean_box(x_27);
lean_inc(x_2);
x_39 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__2___boxed), 17, 8);
lean_closure_set(x_39, 0, x_25);
lean_closure_set(x_39, 1, x_37);
lean_closure_set(x_39, 2, x_32);
lean_closure_set(x_39, 3, x_2);
lean_closure_set(x_39, 4, x_38);
lean_closure_set(x_39, 5, x_18);
lean_closure_set(x_39, 6, x_35);
lean_closure_set(x_39, 7, x_34);
x_40 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__3), 11, 1);
lean_closure_set(x_40, 0, x_30);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Elab_withInfoTreeContext___at___Lean_Elab_Tactic_evalTactic_eval_spec__5(lean_box(0), x_39, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_3, 2);
x_44 = lean_nat_add(x_5, x_43);
x_45 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(x_1, x_2, x_3, x_22, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_42);
return x_45;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_41;
}
}
block_60:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_mk_empty_array_with_capacity(x_48);
lean_inc(x_25);
x_50 = lean_array_push(x_49, x_25);
x_51 = lean_array_push(x_50, x_47);
x_52 = lean_mk_string_unchecked("null", 4, 4);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_box(2);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_51);
x_56 = l_Lean_Syntax_getArg(x_25, x_23);
x_57 = l_Lean_Syntax_isNone(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
x_26 = x_55;
x_27 = x_16;
goto block_46;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_box(0);
x_59 = lean_unbox(x_58);
x_26 = x_55;
x_27 = x_59;
goto block_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_array_push(x_16, x_1);
x_18 = lean_array_push(x_17, x_14);
x_19 = lean_mk_string_unchecked("null", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_box(2);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_18);
x_23 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed), 10, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRWRulesSeq___lam__1), 11, 1);
lean_closure_set(x_28, 0, x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Elab_withInfoTreeContext___at___Lean_Elab_Tactic_evalTactic_eval_spec__5(lean_box(0), x_27, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = l_Lean_Syntax_getArg(x_2, x_31);
x_33 = l_Lean_Syntax_getArgs(x_32);
lean_dec(x_32);
x_34 = lean_array_get_size(x_33);
lean_dec(x_33);
x_35 = lean_nat_add(x_34, x_31);
lean_dec(x_34);
x_36 = lean_nat_shiftr(x_35, x_31);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_31);
x_38 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(x_2, x_3, x_37, x_26, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_26);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
return x_38;
}
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
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__1(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__2___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = lean_unbox(x_5);
lean_dec(x_5);
x_20 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___lam__2(x_1, x_18, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__1(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_withRWRulesSeq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_withRWRulesSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("Rewrite", 7, 7);
x_10 = lean_mk_string_unchecked("Config", 6, 6);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_evalExpr_x27(lean_box(0), x_11, x_1, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1350____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_37 = l_Lean_Parser_Tactic_getConfigItems(x_1);
x_38 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(x_37);
x_39 = l_Array_isEmpty___redArg(x_38);
x_40 = lean_box(1);
if (x_39 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_st_ref_get(x_8, x_9);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_7, 5);
x_46 = l_Lean_replaceRef(x_1, x_45);
lean_dec(x_1);
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
x_49 = lean_ctor_get(x_7, 2);
x_50 = lean_ctor_get(x_7, 3);
x_51 = lean_ctor_get(x_7, 4);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_ctor_get(x_7, 7);
x_54 = lean_ctor_get(x_7, 8);
x_55 = lean_ctor_get(x_7, 9);
x_56 = lean_ctor_get(x_7, 10);
x_57 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_58 = lean_ctor_get(x_7, 11);
x_59 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_60 = lean_ctor_get(x_7, 12);
lean_inc(x_60);
lean_inc(x_58);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_61 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_49);
lean_ctor_set(x_61, 3, x_50);
lean_ctor_set(x_61, 4, x_51);
lean_ctor_set(x_61, 5, x_46);
lean_ctor_set(x_61, 6, x_52);
lean_ctor_set(x_61, 7, x_53);
lean_ctor_set(x_61, 8, x_54);
lean_ctor_set(x_61, 9, x_55);
lean_ctor_set(x_61, 10, x_56);
lean_ctor_set(x_61, 11, x_58);
lean_ctor_set(x_61, 12, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*13, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*13 + 1, x_59);
x_62 = lean_ctor_get(x_43, 0);
lean_inc(x_62);
lean_dec(x_43);
x_63 = lean_mk_string_unchecked("Lean", 4, 4);
x_64 = lean_mk_string_unchecked("Meta", 4, 4);
x_65 = lean_mk_string_unchecked("Rewrite", 7, 7);
x_66 = lean_mk_string_unchecked("Config", 6, 6);
x_67 = l_Lean_Name_mkStr4(x_63, x_64, x_65, x_66);
x_68 = lean_unbox(x_40);
lean_inc(x_67);
x_69 = l_Lean_Environment_contains(x_62, x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_38);
x_70 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = l_Lean_MessageData_ofName(x_67);
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_72);
lean_ctor_set(x_41, 0, x_71);
x_73 = lean_mk_string_unchecked("", 0, 0);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_41);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_75, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_free_object(x_41);
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_81 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_67, x_38, x_3, x_4, x_5, x_6, x_61, x_8, x_44);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
x_85 = l_Lean_Expr_hasSyntheticSorry(x_83);
if (x_85 == 0)
{
uint8_t x_86; 
lean_free_object(x_81);
x_86 = l_Lean_Expr_hasSorry(x_83);
if (x_86 == 0)
{
lean_object* x_87; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_83);
x_87 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(x_83, x_5, x_6, x_61, x_8, x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_83);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = l_Lean_Exception_isInterrupt(x_88);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Exception_isRuntime(x_88);
x_10 = x_61;
x_11 = x_89;
x_12 = x_5;
x_13 = x_88;
x_14 = x_87;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_8;
x_19 = x_83;
x_20 = x_91;
goto block_35;
}
else
{
x_10 = x_61;
x_11 = x_89;
x_12 = x_5;
x_13 = x_88;
x_14 = x_87;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_8;
x_19 = x_83;
x_20 = x_90;
goto block_35;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_83);
x_92 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_93, x_3, x_4, x_5, x_6, x_61, x_8, x_84);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; 
lean_dec(x_83);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_box(2);
x_100 = lean_box(0);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_unbox(x_99);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_103);
lean_ctor_set_uint8(x_102, sizeof(void*)*1 + 1, x_85);
x_104 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*1 + 2, x_104);
lean_ctor_set(x_81, 0, x_102);
return x_81;
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_81, 0);
x_106 = lean_ctor_get(x_81, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_81);
x_107 = l_Lean_Expr_hasSyntheticSorry(x_105);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_Lean_Expr_hasSorry(x_105);
if (x_108 == 0)
{
lean_object* x_109; 
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_105);
x_109 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(x_105, x_5, x_6, x_61, x_8, x_106);
if (lean_obj_tag(x_109) == 0)
{
lean_dec(x_105);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
x_112 = l_Lean_Exception_isInterrupt(x_110);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = l_Lean_Exception_isRuntime(x_110);
x_10 = x_61;
x_11 = x_111;
x_12 = x_5;
x_13 = x_110;
x_14 = x_109;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_8;
x_19 = x_105;
x_20 = x_113;
goto block_35;
}
else
{
x_10 = x_61;
x_11 = x_111;
x_12 = x_5;
x_13 = x_110;
x_14 = x_109;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_8;
x_19 = x_105;
x_20 = x_112;
goto block_35;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_105);
x_114 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_115 = l_Lean_stringToMessageData(x_114);
lean_dec(x_114);
x_116 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_115, x_3, x_4, x_5, x_6, x_61, x_8, x_106);
lean_dec(x_8);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; 
lean_dec(x_105);
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = lean_box(2);
x_122 = lean_box(0);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_124, 0, x_122);
x_125 = lean_unbox(x_121);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_125);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 1, x_107);
x_126 = lean_unbox(x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*1 + 2, x_126);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_106);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_128 = !lean_is_exclusive(x_81);
if (x_128 == 0)
{
return x_81;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_81, 0);
x_130 = lean_ctor_get(x_81, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_81);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_158; 
x_132 = lean_ctor_get(x_41, 0);
x_133 = lean_ctor_get(x_41, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_41);
x_134 = lean_ctor_get(x_7, 5);
x_135 = l_Lean_replaceRef(x_1, x_134);
lean_dec(x_1);
x_136 = lean_ctor_get(x_7, 0);
x_137 = lean_ctor_get(x_7, 1);
x_138 = lean_ctor_get(x_7, 2);
x_139 = lean_ctor_get(x_7, 3);
x_140 = lean_ctor_get(x_7, 4);
x_141 = lean_ctor_get(x_7, 6);
x_142 = lean_ctor_get(x_7, 7);
x_143 = lean_ctor_get(x_7, 8);
x_144 = lean_ctor_get(x_7, 9);
x_145 = lean_ctor_get(x_7, 10);
x_146 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_147 = lean_ctor_get(x_7, 11);
x_148 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_149 = lean_ctor_get(x_7, 12);
lean_inc(x_149);
lean_inc(x_147);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
x_150 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_137);
lean_ctor_set(x_150, 2, x_138);
lean_ctor_set(x_150, 3, x_139);
lean_ctor_set(x_150, 4, x_140);
lean_ctor_set(x_150, 5, x_135);
lean_ctor_set(x_150, 6, x_141);
lean_ctor_set(x_150, 7, x_142);
lean_ctor_set(x_150, 8, x_143);
lean_ctor_set(x_150, 9, x_144);
lean_ctor_set(x_150, 10, x_145);
lean_ctor_set(x_150, 11, x_147);
lean_ctor_set(x_150, 12, x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*13, x_146);
lean_ctor_set_uint8(x_150, sizeof(void*)*13 + 1, x_148);
x_151 = lean_ctor_get(x_132, 0);
lean_inc(x_151);
lean_dec(x_132);
x_152 = lean_mk_string_unchecked("Lean", 4, 4);
x_153 = lean_mk_string_unchecked("Meta", 4, 4);
x_154 = lean_mk_string_unchecked("Rewrite", 7, 7);
x_155 = lean_mk_string_unchecked("Config", 6, 6);
x_156 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_155);
x_157 = lean_unbox(x_40);
lean_inc(x_156);
x_158 = l_Lean_Environment_contains(x_151, x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_38);
x_159 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
x_160 = l_Lean_stringToMessageData(x_159);
lean_dec(x_159);
x_161 = l_Lean_MessageData_ofName(x_156);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_mk_string_unchecked("", 0, 0);
x_164 = l_Lean_stringToMessageData(x_163);
lean_dec(x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_165, x_3, x_4, x_5, x_6, x_150, x_8, x_133);
lean_dec(x_8);
lean_dec(x_150);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
else
{
lean_object* x_171; 
lean_inc(x_8);
lean_inc(x_150);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_171 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_36, x_156, x_38, x_3, x_4, x_5, x_6, x_150, x_8, x_133);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = l_Lean_Expr_hasSyntheticSorry(x_172);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_174);
x_176 = l_Lean_Expr_hasSorry(x_172);
if (x_176 == 0)
{
lean_object* x_177; 
lean_inc(x_8);
lean_inc(x_150);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_172);
x_177 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_Rewrite___hyg_1350_(x_172, x_5, x_6, x_150, x_8, x_173);
if (lean_obj_tag(x_177) == 0)
{
lean_dec(x_172);
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
x_180 = l_Lean_Exception_isInterrupt(x_178);
if (x_180 == 0)
{
uint8_t x_181; 
x_181 = l_Lean_Exception_isRuntime(x_178);
x_10 = x_150;
x_11 = x_179;
x_12 = x_5;
x_13 = x_178;
x_14 = x_177;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_8;
x_19 = x_172;
x_20 = x_181;
goto block_35;
}
else
{
x_10 = x_150;
x_11 = x_179;
x_12 = x_5;
x_13 = x_178;
x_14 = x_177;
x_15 = x_6;
x_16 = x_4;
x_17 = x_3;
x_18 = x_8;
x_19 = x_172;
x_20 = x_180;
goto block_35;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_172);
x_182 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
x_183 = l_Lean_stringToMessageData(x_182);
lean_dec(x_182);
x_184 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_183, x_3, x_4, x_5, x_6, x_150, x_8, x_173);
lean_dec(x_8);
lean_dec(x_150);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; lean_object* x_195; 
lean_dec(x_172);
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_189 = lean_box(2);
x_190 = lean_box(0);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_192, 0, x_190);
x_193 = lean_unbox(x_189);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_193);
lean_ctor_set_uint8(x_192, sizeof(void*)*1 + 1, x_175);
x_194 = lean_unbox(x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*1 + 2, x_194);
if (lean_is_scalar(x_174)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_174;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_173);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_ctor_get(x_171, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_171, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_198 = x_171;
} else {
 lean_dec_ref(x_171);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; lean_object* x_207; 
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_200 = lean_box(2);
x_201 = lean_box(0);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_203, 0, x_201);
x_204 = lean_unbox(x_200);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_204);
x_205 = lean_unbox(x_40);
lean_ctor_set_uint8(x_203, sizeof(void*)*1 + 1, x_205);
x_206 = lean_unbox(x_202);
lean_ctor_set_uint8(x_203, sizeof(void*)*1 + 2, x_206);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_203);
lean_ctor_set(x_207, 1, x_9);
return x_207;
}
block_35:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
x_21 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofExpr(x_19);
x_24 = l_Lean_indentD(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Exception_toMessageData(x_13);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_17, x_16, x_12, x_15, x_10, x_18, x_11);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_16);
return x_34;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabRewriteConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_mk_string_unchecked("rewrite", 7, 7);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_string_unchecked("did not find instance of the pattern in the current goal", 56, 56);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_throwTacticEx___redArg(x_12, x_1, x_16, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_rewriteLocalDecl(x_1, x_2, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(x_4);
lean_inc(x_1);
lean_inc(x_5);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed), 13, 3);
lean_closure_set(x_16, 0, x_5);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_1);
x_17 = lean_box(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_1);
x_19 = l_Lean_Elab_Tactic_withLocation(x_2, x_16, x_18, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(x_12, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed), 10, 0);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Elab_Tactic_expandOptLocation(x_18);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed), 14, 3);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_16);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_unsigned_to_nat(2u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = l_Lean_Elab_Tactic_withRWRulesSeq(x_22, x_24, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_24);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalRewriteSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("rewriteSeq", 10, 10);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalRewriteSeq", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalRewriteSeq", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(71u);
x_8 = lean_unsigned_to_nat(48u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(78u);
x_11 = lean_unsigned_to_nat(91u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(52u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(66u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
