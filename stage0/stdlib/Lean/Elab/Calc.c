// Lean compiler output
// Module: Lean.Elab.Calc
// Imports: Lean.Elab.App
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Meta_throwLetTypeMismatchMessage_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instInhabitedCalcStepView;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabCalcSteps_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_mkCalcTrans_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_useDiagnosticMsg;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_elabCalcSteps_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Expr_getAppNumArgs(x_1);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
x_9 = l_Lean_Expr_appArg_x21(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getCalcRelation_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_getCalcRelation_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_whnf(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 3)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_mk_string_unchecked("unexpected relation type", 24, 24);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = l_Lean_indentExpr(x_1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("", 0, 0);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_24, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed), 8, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_8, x_10, x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_mkCalcTrans_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_string_unchecked("Lean.Elab.Calc", 14, 14);
x_14 = lean_mk_string_unchecked("Lean.Elab.Term.mkCalcTrans", 26, 26);
x_15 = lean_unsigned_to_nat(30u);
x_16 = lean_unsigned_to_nat(53u);
x_17 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_18 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_13, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_19 = l_panic___at___Lean_Elab_Term_mkCalcTrans_spec__0(x_18, x_5, x_6, x_7, x_8, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
x_31 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_4, x_6, x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_33, x_34);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_mk_string_unchecked("Lean.Elab.Calc", 14, 14);
x_39 = lean_mk_string_unchecked("Lean.Elab.Term.mkCalcTrans", 26, 26);
x_40 = lean_unsigned_to_nat(31u);
x_41 = lean_unsigned_to_nat(72u);
x_42 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_43 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
x_44 = l_panic___at___Lean_Elab_Term_mkCalcTrans_spec__0(x_43, x_5, x_6, x_7, x_8, x_37);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_35, 1);
x_50 = lean_ctor_get(x_35, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 1);
x_56 = lean_ctor_get(x_47, 0);
lean_dec(x_56);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_57 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_26, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_52);
x_60 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_52, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_63 = lean_infer_type(x_29, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_66 = lean_infer_type(x_30, x_5, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_55);
x_69 = lean_infer_type(x_55, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_64);
x_72 = l_Lean_Meta_getLevel(x_64, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_67);
x_75 = l_Lean_Meta_getLevel(x_67, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_70);
x_78 = l_Lean_Meta_getLevel(x_70, x_5, x_6, x_7, x_8, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_80);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
x_85 = l_Lean_Expr_sort___override(x_83);
lean_inc(x_70);
x_86 = l_Lean_mkArrow(x_70, x_85, x_7, x_8, x_84);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_64);
x_90 = l_Lean_mkArrow(x_64, x_88, x_7, x_8, x_89);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_ctor_set(x_36, 0, x_92);
x_94 = lean_box(0);
x_95 = lean_box(0);
x_96 = lean_unbox(x_94);
lean_inc(x_5);
x_97 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_96, x_95, x_5, x_6, x_7, x_8, x_93);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_101);
x_102 = l_Lean_Name_mkStr1(x_101);
x_103 = lean_box(0);
lean_ctor_set_tag(x_97, 1);
lean_ctor_set(x_97, 1, x_103);
lean_ctor_set(x_97, 0, x_79);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 1, x_97);
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 1, x_90);
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 1, x_86);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_81);
lean_ctor_set(x_46, 0, x_61);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_46);
lean_ctor_set(x_35, 0, x_58);
lean_inc(x_35);
x_104 = l_Lean_Expr_const___override(x_102, x_35);
x_105 = lean_unsigned_to_nat(6u);
x_106 = lean_mk_empty_array_with_capacity(x_105);
lean_inc(x_64);
x_107 = lean_array_push(x_106, x_64);
lean_inc(x_67);
x_108 = lean_array_push(x_107, x_67);
lean_inc(x_70);
x_109 = lean_array_push(x_108, x_70);
lean_inc(x_26);
x_110 = lean_array_push(x_109, x_26);
lean_inc(x_52);
x_111 = lean_array_push(x_110, x_52);
lean_inc(x_99);
x_112 = lean_array_push(x_111, x_99);
x_113 = l_Lean_mkAppN(x_104, x_112);
lean_dec(x_112);
x_114 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_113);
x_115 = l_Lean_Meta_trySynthInstance(x_113, x_114, x_5, x_6, x_7, x_8, x_100);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_113);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_mk_string_unchecked("trans", 5, 5);
x_120 = l_Lean_Name_mkStr2(x_101, x_119);
x_121 = l_Lean_Expr_const___override(x_120, x_35);
x_122 = lean_unsigned_to_nat(12u);
x_123 = lean_mk_empty_array_with_capacity(x_122);
x_124 = lean_array_push(x_123, x_64);
x_125 = lean_array_push(x_124, x_67);
x_126 = lean_array_push(x_125, x_70);
x_127 = lean_array_push(x_126, x_26);
x_128 = lean_array_push(x_127, x_52);
x_129 = lean_array_push(x_128, x_99);
x_130 = lean_array_push(x_129, x_118);
x_131 = lean_array_push(x_130, x_29);
x_132 = lean_array_push(x_131, x_30);
x_133 = lean_array_push(x_132, x_55);
x_134 = lean_array_push(x_133, x_1);
x_135 = lean_array_push(x_134, x_3);
x_136 = l_Lean_mkAppN(x_121, x_135);
lean_dec(x_135);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_136);
x_137 = lean_infer_type(x_136, x_5, x_6, x_7, x_8, x_117);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_138, x_6, x_139);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_140, 1);
x_144 = l_Lean_Expr_headBeta(x_142);
x_145 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_144, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_136);
lean_free_object(x_47);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
x_150 = l_Lean_indentExpr(x_144);
lean_ctor_set_tag(x_140, 7);
lean_ctor_set(x_140, 1, x_150);
lean_ctor_set(x_140, 0, x_149);
x_151 = lean_mk_string_unchecked("", 0, 0);
x_152 = l_Lean_stringToMessageData(x_151);
lean_dec(x_151);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_152);
lean_ctor_set(x_31, 0, x_140);
x_153 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_147);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
return x_153;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_153);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
uint8_t x_158; 
lean_dec(x_146);
lean_free_object(x_140);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_158 = !lean_is_exclusive(x_145);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_145, 0);
lean_dec(x_159);
lean_ctor_set(x_47, 1, x_144);
lean_ctor_set(x_47, 0, x_136);
lean_ctor_set(x_145, 0, x_47);
return x_145;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_145, 1);
lean_inc(x_160);
lean_dec(x_145);
lean_ctor_set(x_47, 1, x_144);
lean_ctor_set(x_47, 0, x_136);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_47);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_140, 0);
x_163 = lean_ctor_get(x_140, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_140);
x_164 = l_Lean_Expr_headBeta(x_162);
x_165 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_164, x_163);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_136);
lean_free_object(x_47);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_169 = l_Lean_stringToMessageData(x_168);
lean_dec(x_168);
x_170 = l_Lean_indentExpr(x_164);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_mk_string_unchecked("", 0, 0);
x_173 = l_Lean_stringToMessageData(x_172);
lean_dec(x_172);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_173);
lean_ctor_set(x_31, 0, x_171);
x_174 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_167);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_166);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_179 = lean_ctor_get(x_165, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_180 = x_165;
} else {
 lean_dec_ref(x_165);
 x_180 = lean_box(0);
}
lean_ctor_set(x_47, 1, x_164);
lean_ctor_set(x_47, 0, x_136);
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_47);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_136);
lean_free_object(x_47);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_182 = !lean_is_exclusive(x_137);
if (x_182 == 0)
{
return x_137;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_137, 0);
x_184 = lean_ctor_get(x_137, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_137);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_116);
lean_dec(x_35);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_186 = lean_ctor_get(x_115, 1);
lean_inc(x_186);
lean_dec(x_115);
x_187 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = l_Lean_indentExpr(x_113);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_189);
lean_ctor_set(x_31, 0, x_188);
x_190 = lean_mk_string_unchecked("", 0, 0);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
lean_inc(x_191);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_191);
lean_ctor_set(x_21, 0, x_31);
x_192 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_192);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_191);
lean_ctor_set(x_10, 0, x_20);
x_193 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_193;
}
}
else
{
uint8_t x_194; 
lean_dec(x_113);
lean_dec(x_35);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_115);
if (x_194 == 0)
{
return x_115;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_115, 0);
x_196 = lean_ctor_get(x_115, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_115);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_198 = lean_ctor_get(x_97, 0);
x_199 = lean_ctor_get(x_97, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_97);
x_200 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_200);
x_201 = l_Lean_Name_mkStr1(x_200);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_79);
lean_ctor_set(x_203, 1, x_202);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 1, x_203);
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 1, x_90);
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 1, x_86);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_81);
lean_ctor_set(x_46, 0, x_61);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_46);
lean_ctor_set(x_35, 0, x_58);
lean_inc(x_35);
x_204 = l_Lean_Expr_const___override(x_201, x_35);
x_205 = lean_unsigned_to_nat(6u);
x_206 = lean_mk_empty_array_with_capacity(x_205);
lean_inc(x_64);
x_207 = lean_array_push(x_206, x_64);
lean_inc(x_67);
x_208 = lean_array_push(x_207, x_67);
lean_inc(x_70);
x_209 = lean_array_push(x_208, x_70);
lean_inc(x_26);
x_210 = lean_array_push(x_209, x_26);
lean_inc(x_52);
x_211 = lean_array_push(x_210, x_52);
lean_inc(x_198);
x_212 = lean_array_push(x_211, x_198);
x_213 = l_Lean_mkAppN(x_204, x_212);
lean_dec(x_212);
x_214 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_213);
x_215 = l_Lean_Meta_trySynthInstance(x_213, x_214, x_5, x_6, x_7, x_8, x_199);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
if (lean_obj_tag(x_216) == 1)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_213);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_mk_string_unchecked("trans", 5, 5);
x_220 = l_Lean_Name_mkStr2(x_200, x_219);
x_221 = l_Lean_Expr_const___override(x_220, x_35);
x_222 = lean_unsigned_to_nat(12u);
x_223 = lean_mk_empty_array_with_capacity(x_222);
x_224 = lean_array_push(x_223, x_64);
x_225 = lean_array_push(x_224, x_67);
x_226 = lean_array_push(x_225, x_70);
x_227 = lean_array_push(x_226, x_26);
x_228 = lean_array_push(x_227, x_52);
x_229 = lean_array_push(x_228, x_198);
x_230 = lean_array_push(x_229, x_218);
x_231 = lean_array_push(x_230, x_29);
x_232 = lean_array_push(x_231, x_30);
x_233 = lean_array_push(x_232, x_55);
x_234 = lean_array_push(x_233, x_1);
x_235 = lean_array_push(x_234, x_3);
x_236 = l_Lean_mkAppN(x_221, x_235);
lean_dec(x_235);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_236);
x_237 = lean_infer_type(x_236, x_5, x_6, x_7, x_8, x_217);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_238, x_6, x_239);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = l_Lean_Expr_headBeta(x_241);
x_245 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_244, x_242);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_236);
lean_free_object(x_47);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_249 = l_Lean_stringToMessageData(x_248);
lean_dec(x_248);
x_250 = l_Lean_indentExpr(x_244);
if (lean_is_scalar(x_243)) {
 x_251 = lean_alloc_ctor(7, 2, 0);
} else {
 x_251 = x_243;
 lean_ctor_set_tag(x_251, 7);
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_mk_string_unchecked("", 0, 0);
x_253 = l_Lean_stringToMessageData(x_252);
lean_dec(x_252);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_253);
lean_ctor_set(x_31, 0, x_251);
x_254 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_247);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
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
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_246);
lean_dec(x_243);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_259 = lean_ctor_get(x_245, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_260 = x_245;
} else {
 lean_dec_ref(x_245);
 x_260 = lean_box(0);
}
lean_ctor_set(x_47, 1, x_244);
lean_ctor_set(x_47, 0, x_236);
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_47);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_236);
lean_free_object(x_47);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_262 = lean_ctor_get(x_237, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_237, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_264 = x_237;
} else {
 lean_dec_ref(x_237);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_216);
lean_dec(x_35);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_215, 1);
lean_inc(x_266);
lean_dec(x_215);
x_267 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_268 = l_Lean_stringToMessageData(x_267);
lean_dec(x_267);
x_269 = l_Lean_indentExpr(x_213);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_269);
lean_ctor_set(x_31, 0, x_268);
x_270 = lean_mk_string_unchecked("", 0, 0);
x_271 = l_Lean_stringToMessageData(x_270);
lean_dec(x_270);
lean_inc(x_271);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_271);
lean_ctor_set(x_21, 0, x_31);
x_272 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_272);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_271);
lean_ctor_set(x_10, 0, x_20);
x_273 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_266);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_213);
lean_dec(x_35);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_274 = lean_ctor_get(x_215, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_215, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_276 = x_215;
} else {
 lean_dec_ref(x_215);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_278 = lean_ctor_get(x_90, 0);
x_279 = lean_ctor_get(x_90, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_90);
lean_ctor_set(x_36, 0, x_278);
x_280 = lean_box(0);
x_281 = lean_box(0);
x_282 = lean_unbox(x_280);
lean_inc(x_5);
x_283 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_282, x_281, x_5, x_6, x_7, x_8, x_279);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_286 = x_283;
} else {
 lean_dec_ref(x_283);
 x_286 = lean_box(0);
}
x_287 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_287);
x_288 = l_Lean_Name_mkStr1(x_287);
x_289 = lean_box(0);
if (lean_is_scalar(x_286)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_286;
 lean_ctor_set_tag(x_290, 1);
}
lean_ctor_set(x_290, 0, x_79);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_76);
lean_ctor_set(x_291, 1, x_290);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 1, x_291);
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 1, x_86);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_81);
lean_ctor_set(x_46, 0, x_61);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_46);
lean_ctor_set(x_35, 0, x_58);
lean_inc(x_35);
x_292 = l_Lean_Expr_const___override(x_288, x_35);
x_293 = lean_unsigned_to_nat(6u);
x_294 = lean_mk_empty_array_with_capacity(x_293);
lean_inc(x_64);
x_295 = lean_array_push(x_294, x_64);
lean_inc(x_67);
x_296 = lean_array_push(x_295, x_67);
lean_inc(x_70);
x_297 = lean_array_push(x_296, x_70);
lean_inc(x_26);
x_298 = lean_array_push(x_297, x_26);
lean_inc(x_52);
x_299 = lean_array_push(x_298, x_52);
lean_inc(x_284);
x_300 = lean_array_push(x_299, x_284);
x_301 = l_Lean_mkAppN(x_292, x_300);
lean_dec(x_300);
x_302 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_301);
x_303 = l_Lean_Meta_trySynthInstance(x_301, x_302, x_5, x_6, x_7, x_8, x_285);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
if (lean_obj_tag(x_304) == 1)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_301);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_ctor_get(x_304, 0);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_mk_string_unchecked("trans", 5, 5);
x_308 = l_Lean_Name_mkStr2(x_287, x_307);
x_309 = l_Lean_Expr_const___override(x_308, x_35);
x_310 = lean_unsigned_to_nat(12u);
x_311 = lean_mk_empty_array_with_capacity(x_310);
x_312 = lean_array_push(x_311, x_64);
x_313 = lean_array_push(x_312, x_67);
x_314 = lean_array_push(x_313, x_70);
x_315 = lean_array_push(x_314, x_26);
x_316 = lean_array_push(x_315, x_52);
x_317 = lean_array_push(x_316, x_284);
x_318 = lean_array_push(x_317, x_306);
x_319 = lean_array_push(x_318, x_29);
x_320 = lean_array_push(x_319, x_30);
x_321 = lean_array_push(x_320, x_55);
x_322 = lean_array_push(x_321, x_1);
x_323 = lean_array_push(x_322, x_3);
x_324 = l_Lean_mkAppN(x_309, x_323);
lean_dec(x_323);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_324);
x_325 = lean_infer_type(x_324, x_5, x_6, x_7, x_8, x_305);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_326, x_6, x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_331 = x_328;
} else {
 lean_dec_ref(x_328);
 x_331 = lean_box(0);
}
x_332 = l_Lean_Expr_headBeta(x_329);
x_333 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_332, x_330);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_324);
lean_free_object(x_47);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_337 = l_Lean_stringToMessageData(x_336);
lean_dec(x_336);
x_338 = l_Lean_indentExpr(x_332);
if (lean_is_scalar(x_331)) {
 x_339 = lean_alloc_ctor(7, 2, 0);
} else {
 x_339 = x_331;
 lean_ctor_set_tag(x_339, 7);
}
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_mk_string_unchecked("", 0, 0);
x_341 = l_Lean_stringToMessageData(x_340);
lean_dec(x_340);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_341);
lean_ctor_set(x_31, 0, x_339);
x_342 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_335);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_345 = x_342;
} else {
 lean_dec_ref(x_342);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_334);
lean_dec(x_331);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_347 = lean_ctor_get(x_333, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_348 = x_333;
} else {
 lean_dec_ref(x_333);
 x_348 = lean_box(0);
}
lean_ctor_set(x_47, 1, x_332);
lean_ctor_set(x_47, 0, x_324);
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_47);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_324);
lean_free_object(x_47);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_350 = lean_ctor_get(x_325, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_325, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_352 = x_325;
} else {
 lean_dec_ref(x_325);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_304);
lean_dec(x_35);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_354 = lean_ctor_get(x_303, 1);
lean_inc(x_354);
lean_dec(x_303);
x_355 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_356 = l_Lean_stringToMessageData(x_355);
lean_dec(x_355);
x_357 = l_Lean_indentExpr(x_301);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_357);
lean_ctor_set(x_31, 0, x_356);
x_358 = lean_mk_string_unchecked("", 0, 0);
x_359 = l_Lean_stringToMessageData(x_358);
lean_dec(x_358);
lean_inc(x_359);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_359);
lean_ctor_set(x_21, 0, x_31);
x_360 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_360);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_359);
lean_ctor_set(x_10, 0, x_20);
x_361 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_354);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_301);
lean_dec(x_35);
lean_dec(x_287);
lean_dec(x_284);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_362 = lean_ctor_get(x_303, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_303, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_364 = x_303;
} else {
 lean_dec_ref(x_303);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_366 = lean_ctor_get(x_86, 0);
x_367 = lean_ctor_get(x_86, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_86);
lean_inc(x_64);
x_368 = l_Lean_mkArrow(x_64, x_366, x_7, x_8, x_367);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_371 = x_368;
} else {
 lean_dec_ref(x_368);
 x_371 = lean_box(0);
}
lean_ctor_set(x_36, 0, x_369);
x_372 = lean_box(0);
x_373 = lean_box(0);
x_374 = lean_unbox(x_372);
lean_inc(x_5);
x_375 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_374, x_373, x_5, x_6, x_7, x_8, x_370);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
x_379 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_379);
x_380 = l_Lean_Name_mkStr1(x_379);
x_381 = lean_box(0);
if (lean_is_scalar(x_378)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_378;
 lean_ctor_set_tag(x_382, 1);
}
lean_ctor_set(x_382, 0, x_79);
lean_ctor_set(x_382, 1, x_381);
if (lean_is_scalar(x_371)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_371;
 lean_ctor_set_tag(x_383, 1);
}
lean_ctor_set(x_383, 0, x_76);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_73);
lean_ctor_set(x_384, 1, x_383);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 1, x_384);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_81);
lean_ctor_set(x_46, 0, x_61);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_46);
lean_ctor_set(x_35, 0, x_58);
lean_inc(x_35);
x_385 = l_Lean_Expr_const___override(x_380, x_35);
x_386 = lean_unsigned_to_nat(6u);
x_387 = lean_mk_empty_array_with_capacity(x_386);
lean_inc(x_64);
x_388 = lean_array_push(x_387, x_64);
lean_inc(x_67);
x_389 = lean_array_push(x_388, x_67);
lean_inc(x_70);
x_390 = lean_array_push(x_389, x_70);
lean_inc(x_26);
x_391 = lean_array_push(x_390, x_26);
lean_inc(x_52);
x_392 = lean_array_push(x_391, x_52);
lean_inc(x_376);
x_393 = lean_array_push(x_392, x_376);
x_394 = l_Lean_mkAppN(x_385, x_393);
lean_dec(x_393);
x_395 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_394);
x_396 = l_Lean_Meta_trySynthInstance(x_394, x_395, x_5, x_6, x_7, x_8, x_377);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
if (lean_obj_tag(x_397) == 1)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_394);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_mk_string_unchecked("trans", 5, 5);
x_401 = l_Lean_Name_mkStr2(x_379, x_400);
x_402 = l_Lean_Expr_const___override(x_401, x_35);
x_403 = lean_unsigned_to_nat(12u);
x_404 = lean_mk_empty_array_with_capacity(x_403);
x_405 = lean_array_push(x_404, x_64);
x_406 = lean_array_push(x_405, x_67);
x_407 = lean_array_push(x_406, x_70);
x_408 = lean_array_push(x_407, x_26);
x_409 = lean_array_push(x_408, x_52);
x_410 = lean_array_push(x_409, x_376);
x_411 = lean_array_push(x_410, x_399);
x_412 = lean_array_push(x_411, x_29);
x_413 = lean_array_push(x_412, x_30);
x_414 = lean_array_push(x_413, x_55);
x_415 = lean_array_push(x_414, x_1);
x_416 = lean_array_push(x_415, x_3);
x_417 = l_Lean_mkAppN(x_402, x_416);
lean_dec(x_416);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_417);
x_418 = lean_infer_type(x_417, x_5, x_6, x_7, x_8, x_398);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_419, x_6, x_420);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_424 = x_421;
} else {
 lean_dec_ref(x_421);
 x_424 = lean_box(0);
}
x_425 = l_Lean_Expr_headBeta(x_422);
x_426 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_425, x_423);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_417);
lean_free_object(x_47);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_430 = l_Lean_stringToMessageData(x_429);
lean_dec(x_429);
x_431 = l_Lean_indentExpr(x_425);
if (lean_is_scalar(x_424)) {
 x_432 = lean_alloc_ctor(7, 2, 0);
} else {
 x_432 = x_424;
 lean_ctor_set_tag(x_432, 7);
}
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
x_433 = lean_mk_string_unchecked("", 0, 0);
x_434 = l_Lean_stringToMessageData(x_433);
lean_dec(x_433);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_434);
lean_ctor_set(x_31, 0, x_432);
x_435 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_428);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_438 = x_435;
} else {
 lean_dec_ref(x_435);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_427);
lean_dec(x_424);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_440 = lean_ctor_get(x_426, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_441 = x_426;
} else {
 lean_dec_ref(x_426);
 x_441 = lean_box(0);
}
lean_ctor_set(x_47, 1, x_425);
lean_ctor_set(x_47, 0, x_417);
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_47);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_417);
lean_free_object(x_47);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_443 = lean_ctor_get(x_418, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_418, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_445 = x_418;
} else {
 lean_dec_ref(x_418);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_397);
lean_dec(x_35);
lean_dec(x_379);
lean_dec(x_376);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_447 = lean_ctor_get(x_396, 1);
lean_inc(x_447);
lean_dec(x_396);
x_448 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_449 = l_Lean_stringToMessageData(x_448);
lean_dec(x_448);
x_450 = l_Lean_indentExpr(x_394);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_450);
lean_ctor_set(x_31, 0, x_449);
x_451 = lean_mk_string_unchecked("", 0, 0);
x_452 = l_Lean_stringToMessageData(x_451);
lean_dec(x_451);
lean_inc(x_452);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_452);
lean_ctor_set(x_21, 0, x_31);
x_453 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_453);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_452);
lean_ctor_set(x_10, 0, x_20);
x_454 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_447);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_454;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_394);
lean_dec(x_35);
lean_dec(x_379);
lean_dec(x_376);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_455 = lean_ctor_get(x_396, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_396, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_457 = x_396;
} else {
 lean_dec_ref(x_396);
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
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_459 = lean_ctor_get(x_81, 0);
x_460 = lean_ctor_get(x_81, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_81);
lean_inc(x_459);
x_461 = l_Lean_Expr_sort___override(x_459);
lean_inc(x_70);
x_462 = l_Lean_mkArrow(x_70, x_461, x_7, x_8, x_460);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_465 = x_462;
} else {
 lean_dec_ref(x_462);
 x_465 = lean_box(0);
}
lean_inc(x_64);
x_466 = l_Lean_mkArrow(x_64, x_463, x_7, x_8, x_464);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_469 = x_466;
} else {
 lean_dec_ref(x_466);
 x_469 = lean_box(0);
}
lean_ctor_set(x_36, 0, x_467);
x_470 = lean_box(0);
x_471 = lean_box(0);
x_472 = lean_unbox(x_470);
lean_inc(x_5);
x_473 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_472, x_471, x_5, x_6, x_7, x_8, x_468);
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
x_477 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_477);
x_478 = l_Lean_Name_mkStr1(x_477);
x_479 = lean_box(0);
if (lean_is_scalar(x_476)) {
 x_480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_480 = x_476;
 lean_ctor_set_tag(x_480, 1);
}
lean_ctor_set(x_480, 0, x_79);
lean_ctor_set(x_480, 1, x_479);
if (lean_is_scalar(x_469)) {
 x_481 = lean_alloc_ctor(1, 2, 0);
} else {
 x_481 = x_469;
 lean_ctor_set_tag(x_481, 1);
}
lean_ctor_set(x_481, 0, x_76);
lean_ctor_set(x_481, 1, x_480);
if (lean_is_scalar(x_465)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_465;
 lean_ctor_set_tag(x_482, 1);
}
lean_ctor_set(x_482, 0, x_73);
lean_ctor_set(x_482, 1, x_481);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_459);
lean_ctor_set(x_483, 1, x_482);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_483);
lean_ctor_set(x_46, 0, x_61);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_46);
lean_ctor_set(x_35, 0, x_58);
lean_inc(x_35);
x_484 = l_Lean_Expr_const___override(x_478, x_35);
x_485 = lean_unsigned_to_nat(6u);
x_486 = lean_mk_empty_array_with_capacity(x_485);
lean_inc(x_64);
x_487 = lean_array_push(x_486, x_64);
lean_inc(x_67);
x_488 = lean_array_push(x_487, x_67);
lean_inc(x_70);
x_489 = lean_array_push(x_488, x_70);
lean_inc(x_26);
x_490 = lean_array_push(x_489, x_26);
lean_inc(x_52);
x_491 = lean_array_push(x_490, x_52);
lean_inc(x_474);
x_492 = lean_array_push(x_491, x_474);
x_493 = l_Lean_mkAppN(x_484, x_492);
lean_dec(x_492);
x_494 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_493);
x_495 = l_Lean_Meta_trySynthInstance(x_493, x_494, x_5, x_6, x_7, x_8, x_475);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 1)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_493);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_ctor_get(x_496, 0);
lean_inc(x_498);
lean_dec(x_496);
x_499 = lean_mk_string_unchecked("trans", 5, 5);
x_500 = l_Lean_Name_mkStr2(x_477, x_499);
x_501 = l_Lean_Expr_const___override(x_500, x_35);
x_502 = lean_unsigned_to_nat(12u);
x_503 = lean_mk_empty_array_with_capacity(x_502);
x_504 = lean_array_push(x_503, x_64);
x_505 = lean_array_push(x_504, x_67);
x_506 = lean_array_push(x_505, x_70);
x_507 = lean_array_push(x_506, x_26);
x_508 = lean_array_push(x_507, x_52);
x_509 = lean_array_push(x_508, x_474);
x_510 = lean_array_push(x_509, x_498);
x_511 = lean_array_push(x_510, x_29);
x_512 = lean_array_push(x_511, x_30);
x_513 = lean_array_push(x_512, x_55);
x_514 = lean_array_push(x_513, x_1);
x_515 = lean_array_push(x_514, x_3);
x_516 = l_Lean_mkAppN(x_501, x_515);
lean_dec(x_515);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_516);
x_517 = lean_infer_type(x_516, x_5, x_6, x_7, x_8, x_497);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
x_520 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_518, x_6, x_519);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_523 = x_520;
} else {
 lean_dec_ref(x_520);
 x_523 = lean_box(0);
}
x_524 = l_Lean_Expr_headBeta(x_521);
x_525 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_524, x_522);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_516);
lean_free_object(x_47);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_529 = l_Lean_stringToMessageData(x_528);
lean_dec(x_528);
x_530 = l_Lean_indentExpr(x_524);
if (lean_is_scalar(x_523)) {
 x_531 = lean_alloc_ctor(7, 2, 0);
} else {
 x_531 = x_523;
 lean_ctor_set_tag(x_531, 7);
}
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
x_532 = lean_mk_string_unchecked("", 0, 0);
x_533 = l_Lean_stringToMessageData(x_532);
lean_dec(x_532);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_533);
lean_ctor_set(x_31, 0, x_531);
x_534 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_537 = x_534;
} else {
 lean_dec_ref(x_534);
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
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_526);
lean_dec(x_523);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_539 = lean_ctor_get(x_525, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_540 = x_525;
} else {
 lean_dec_ref(x_525);
 x_540 = lean_box(0);
}
lean_ctor_set(x_47, 1, x_524);
lean_ctor_set(x_47, 0, x_516);
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_540;
}
lean_ctor_set(x_541, 0, x_47);
lean_ctor_set(x_541, 1, x_539);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_516);
lean_free_object(x_47);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_542 = lean_ctor_get(x_517, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_517, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 x_544 = x_517;
} else {
 lean_dec_ref(x_517);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_542);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_496);
lean_dec(x_35);
lean_dec(x_477);
lean_dec(x_474);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_546 = lean_ctor_get(x_495, 1);
lean_inc(x_546);
lean_dec(x_495);
x_547 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_548 = l_Lean_stringToMessageData(x_547);
lean_dec(x_547);
x_549 = l_Lean_indentExpr(x_493);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_549);
lean_ctor_set(x_31, 0, x_548);
x_550 = lean_mk_string_unchecked("", 0, 0);
x_551 = l_Lean_stringToMessageData(x_550);
lean_dec(x_550);
lean_inc(x_551);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_551);
lean_ctor_set(x_21, 0, x_31);
x_552 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_552);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_551);
lean_ctor_set(x_10, 0, x_20);
x_553 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_546);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_553;
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_493);
lean_dec(x_35);
lean_dec(x_477);
lean_dec(x_474);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_free_object(x_47);
lean_dec(x_55);
lean_dec(x_52);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_554 = lean_ctor_get(x_495, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_495, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_556 = x_495;
} else {
 lean_dec_ref(x_495);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_555);
return x_557;
}
}
}
else
{
uint8_t x_558; 
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_free_object(x_47);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_558 = !lean_is_exclusive(x_78);
if (x_558 == 0)
{
return x_78;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_78, 0);
x_560 = lean_ctor_get(x_78, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_78);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
return x_561;
}
}
}
else
{
uint8_t x_562; 
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_free_object(x_47);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_562 = !lean_is_exclusive(x_75);
if (x_562 == 0)
{
return x_75;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_75, 0);
x_564 = lean_ctor_get(x_75, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_75);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
}
else
{
uint8_t x_566; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_free_object(x_47);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_566 = !lean_is_exclusive(x_72);
if (x_566 == 0)
{
return x_72;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_72, 0);
x_568 = lean_ctor_get(x_72, 1);
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_72);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_567);
lean_ctor_set(x_569, 1, x_568);
return x_569;
}
}
}
else
{
uint8_t x_570; 
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_free_object(x_47);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_570 = !lean_is_exclusive(x_69);
if (x_570 == 0)
{
return x_69;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_571 = lean_ctor_get(x_69, 0);
x_572 = lean_ctor_get(x_69, 1);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_69);
x_573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
return x_573;
}
}
}
else
{
uint8_t x_574; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_58);
lean_free_object(x_47);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_574 = !lean_is_exclusive(x_66);
if (x_574 == 0)
{
return x_66;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_66, 0);
x_576 = lean_ctor_get(x_66, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_66);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set(x_577, 1, x_576);
return x_577;
}
}
}
else
{
uint8_t x_578; 
lean_dec(x_61);
lean_dec(x_58);
lean_free_object(x_47);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_578 = !lean_is_exclusive(x_63);
if (x_578 == 0)
{
return x_63;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_63, 0);
x_580 = lean_ctor_get(x_63, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_63);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
return x_581;
}
}
}
else
{
uint8_t x_582; 
lean_dec(x_58);
lean_free_object(x_47);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_582 = !lean_is_exclusive(x_60);
if (x_582 == 0)
{
return x_60;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_60, 0);
x_584 = lean_ctor_get(x_60, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_60);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
else
{
uint8_t x_586; 
lean_free_object(x_47);
lean_dec(x_55);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_586 = !lean_is_exclusive(x_57);
if (x_586 == 0)
{
return x_57;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_57, 0);
x_588 = lean_ctor_get(x_57, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_57);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
return x_589;
}
}
}
else
{
lean_object* x_590; lean_object* x_591; 
x_590 = lean_ctor_get(x_47, 1);
lean_inc(x_590);
lean_dec(x_47);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_591 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_26, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_52);
x_594 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_52, x_5, x_6, x_7, x_8, x_593);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
lean_dec(x_594);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_597 = lean_infer_type(x_29, x_5, x_6, x_7, x_8, x_596);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_597, 1);
lean_inc(x_599);
lean_dec(x_597);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_600 = lean_infer_type(x_30, x_5, x_6, x_7, x_8, x_599);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_590);
x_603 = lean_infer_type(x_590, x_5, x_6, x_7, x_8, x_602);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_598);
x_606 = l_Lean_Meta_getLevel(x_598, x_5, x_6, x_7, x_8, x_605);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_601);
x_609 = l_Lean_Meta_getLevel(x_601, x_5, x_6, x_7, x_8, x_608);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_604);
x_612 = l_Lean_Meta_getLevel(x_604, x_5, x_6, x_7, x_8, x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_614);
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_615, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_618 = x_615;
} else {
 lean_dec_ref(x_615);
 x_618 = lean_box(0);
}
lean_inc(x_616);
x_619 = l_Lean_Expr_sort___override(x_616);
lean_inc(x_604);
x_620 = l_Lean_mkArrow(x_604, x_619, x_7, x_8, x_617);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_623 = x_620;
} else {
 lean_dec_ref(x_620);
 x_623 = lean_box(0);
}
lean_inc(x_598);
x_624 = l_Lean_mkArrow(x_598, x_621, x_7, x_8, x_622);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_627 = x_624;
} else {
 lean_dec_ref(x_624);
 x_627 = lean_box(0);
}
lean_ctor_set(x_36, 0, x_625);
x_628 = lean_box(0);
x_629 = lean_box(0);
x_630 = lean_unbox(x_628);
lean_inc(x_5);
x_631 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_630, x_629, x_5, x_6, x_7, x_8, x_626);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_634 = x_631;
} else {
 lean_dec_ref(x_631);
 x_634 = lean_box(0);
}
x_635 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_635);
x_636 = l_Lean_Name_mkStr1(x_635);
x_637 = lean_box(0);
if (lean_is_scalar(x_634)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_634;
 lean_ctor_set_tag(x_638, 1);
}
lean_ctor_set(x_638, 0, x_613);
lean_ctor_set(x_638, 1, x_637);
if (lean_is_scalar(x_627)) {
 x_639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_639 = x_627;
 lean_ctor_set_tag(x_639, 1);
}
lean_ctor_set(x_639, 0, x_610);
lean_ctor_set(x_639, 1, x_638);
if (lean_is_scalar(x_623)) {
 x_640 = lean_alloc_ctor(1, 2, 0);
} else {
 x_640 = x_623;
 lean_ctor_set_tag(x_640, 1);
}
lean_ctor_set(x_640, 0, x_607);
lean_ctor_set(x_640, 1, x_639);
if (lean_is_scalar(x_618)) {
 x_641 = lean_alloc_ctor(1, 2, 0);
} else {
 x_641 = x_618;
 lean_ctor_set_tag(x_641, 1);
}
lean_ctor_set(x_641, 0, x_616);
lean_ctor_set(x_641, 1, x_640);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_641);
lean_ctor_set(x_46, 0, x_595);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_46);
lean_ctor_set(x_35, 0, x_592);
lean_inc(x_35);
x_642 = l_Lean_Expr_const___override(x_636, x_35);
x_643 = lean_unsigned_to_nat(6u);
x_644 = lean_mk_empty_array_with_capacity(x_643);
lean_inc(x_598);
x_645 = lean_array_push(x_644, x_598);
lean_inc(x_601);
x_646 = lean_array_push(x_645, x_601);
lean_inc(x_604);
x_647 = lean_array_push(x_646, x_604);
lean_inc(x_26);
x_648 = lean_array_push(x_647, x_26);
lean_inc(x_52);
x_649 = lean_array_push(x_648, x_52);
lean_inc(x_632);
x_650 = lean_array_push(x_649, x_632);
x_651 = l_Lean_mkAppN(x_642, x_650);
lean_dec(x_650);
x_652 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_651);
x_653 = l_Lean_Meta_trySynthInstance(x_651, x_652, x_5, x_6, x_7, x_8, x_633);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
if (lean_obj_tag(x_654) == 1)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_651);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_656 = lean_ctor_get(x_654, 0);
lean_inc(x_656);
lean_dec(x_654);
x_657 = lean_mk_string_unchecked("trans", 5, 5);
x_658 = l_Lean_Name_mkStr2(x_635, x_657);
x_659 = l_Lean_Expr_const___override(x_658, x_35);
x_660 = lean_unsigned_to_nat(12u);
x_661 = lean_mk_empty_array_with_capacity(x_660);
x_662 = lean_array_push(x_661, x_598);
x_663 = lean_array_push(x_662, x_601);
x_664 = lean_array_push(x_663, x_604);
x_665 = lean_array_push(x_664, x_26);
x_666 = lean_array_push(x_665, x_52);
x_667 = lean_array_push(x_666, x_632);
x_668 = lean_array_push(x_667, x_656);
x_669 = lean_array_push(x_668, x_29);
x_670 = lean_array_push(x_669, x_30);
x_671 = lean_array_push(x_670, x_590);
x_672 = lean_array_push(x_671, x_1);
x_673 = lean_array_push(x_672, x_3);
x_674 = l_Lean_mkAppN(x_659, x_673);
lean_dec(x_673);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_674);
x_675 = lean_infer_type(x_674, x_5, x_6, x_7, x_8, x_655);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_678 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_676, x_6, x_677);
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_681 = x_678;
} else {
 lean_dec_ref(x_678);
 x_681 = lean_box(0);
}
x_682 = l_Lean_Expr_headBeta(x_679);
x_683 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_682, x_680);
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_674);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec(x_683);
x_686 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_687 = l_Lean_stringToMessageData(x_686);
lean_dec(x_686);
x_688 = l_Lean_indentExpr(x_682);
if (lean_is_scalar(x_681)) {
 x_689 = lean_alloc_ctor(7, 2, 0);
} else {
 x_689 = x_681;
 lean_ctor_set_tag(x_689, 7);
}
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
x_690 = lean_mk_string_unchecked("", 0, 0);
x_691 = l_Lean_stringToMessageData(x_690);
lean_dec(x_690);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_691);
lean_ctor_set(x_31, 0, x_689);
x_692 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_685);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_692)) {
 lean_ctor_release(x_692, 0);
 lean_ctor_release(x_692, 1);
 x_695 = x_692;
} else {
 lean_dec_ref(x_692);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 2, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_693);
lean_ctor_set(x_696, 1, x_694);
return x_696;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_684);
lean_dec(x_681);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_697 = lean_ctor_get(x_683, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_698 = x_683;
} else {
 lean_dec_ref(x_683);
 x_698 = lean_box(0);
}
x_699 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_699, 0, x_674);
lean_ctor_set(x_699, 1, x_682);
if (lean_is_scalar(x_698)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_698;
}
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_697);
return x_700;
}
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_674);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_701 = lean_ctor_get(x_675, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_675, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 x_703 = x_675;
} else {
 lean_dec_ref(x_675);
 x_703 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_703;
}
lean_ctor_set(x_704, 0, x_701);
lean_ctor_set(x_704, 1, x_702);
return x_704;
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_654);
lean_dec(x_35);
lean_dec(x_635);
lean_dec(x_632);
lean_dec(x_604);
lean_dec(x_601);
lean_dec(x_598);
lean_dec(x_590);
lean_dec(x_52);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_705 = lean_ctor_get(x_653, 1);
lean_inc(x_705);
lean_dec(x_653);
x_706 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_707 = l_Lean_stringToMessageData(x_706);
lean_dec(x_706);
x_708 = l_Lean_indentExpr(x_651);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_708);
lean_ctor_set(x_31, 0, x_707);
x_709 = lean_mk_string_unchecked("", 0, 0);
x_710 = l_Lean_stringToMessageData(x_709);
lean_dec(x_709);
lean_inc(x_710);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_710);
lean_ctor_set(x_21, 0, x_31);
x_711 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_711);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_710);
lean_ctor_set(x_10, 0, x_20);
x_712 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_705);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_712;
}
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_651);
lean_dec(x_35);
lean_dec(x_635);
lean_dec(x_632);
lean_dec(x_604);
lean_dec(x_601);
lean_dec(x_598);
lean_dec(x_590);
lean_dec(x_52);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_713 = lean_ctor_get(x_653, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_653, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 lean_ctor_release(x_653, 1);
 x_715 = x_653;
} else {
 lean_dec_ref(x_653);
 x_715 = lean_box(0);
}
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(1, 2, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_713);
lean_ctor_set(x_716, 1, x_714);
return x_716;
}
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_610);
lean_dec(x_607);
lean_dec(x_604);
lean_dec(x_601);
lean_dec(x_598);
lean_dec(x_595);
lean_dec(x_592);
lean_dec(x_590);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_717 = lean_ctor_get(x_612, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_612, 1);
lean_inc(x_718);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_719 = x_612;
} else {
 lean_dec_ref(x_612);
 x_719 = lean_box(0);
}
if (lean_is_scalar(x_719)) {
 x_720 = lean_alloc_ctor(1, 2, 0);
} else {
 x_720 = x_719;
}
lean_ctor_set(x_720, 0, x_717);
lean_ctor_set(x_720, 1, x_718);
return x_720;
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_607);
lean_dec(x_604);
lean_dec(x_601);
lean_dec(x_598);
lean_dec(x_595);
lean_dec(x_592);
lean_dec(x_590);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_721 = lean_ctor_get(x_609, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_609, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_723 = x_609;
} else {
 lean_dec_ref(x_609);
 x_723 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_724 = x_723;
}
lean_ctor_set(x_724, 0, x_721);
lean_ctor_set(x_724, 1, x_722);
return x_724;
}
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_604);
lean_dec(x_601);
lean_dec(x_598);
lean_dec(x_595);
lean_dec(x_592);
lean_dec(x_590);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_725 = lean_ctor_get(x_606, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_606, 1);
lean_inc(x_726);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_727 = x_606;
} else {
 lean_dec_ref(x_606);
 x_727 = lean_box(0);
}
if (lean_is_scalar(x_727)) {
 x_728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_728 = x_727;
}
lean_ctor_set(x_728, 0, x_725);
lean_ctor_set(x_728, 1, x_726);
return x_728;
}
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_601);
lean_dec(x_598);
lean_dec(x_595);
lean_dec(x_592);
lean_dec(x_590);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_729 = lean_ctor_get(x_603, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_603, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_731 = x_603;
} else {
 lean_dec_ref(x_603);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(1, 2, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_729);
lean_ctor_set(x_732, 1, x_730);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_598);
lean_dec(x_595);
lean_dec(x_592);
lean_dec(x_590);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_733 = lean_ctor_get(x_600, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_600, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_735 = x_600;
} else {
 lean_dec_ref(x_600);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_734);
return x_736;
}
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_595);
lean_dec(x_592);
lean_dec(x_590);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_737 = lean_ctor_get(x_597, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_597, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_739 = x_597;
} else {
 lean_dec_ref(x_597);
 x_739 = lean_box(0);
}
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_738);
return x_740;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_592);
lean_dec(x_590);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_741 = lean_ctor_get(x_594, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_594, 1);
lean_inc(x_742);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_743 = x_594;
} else {
 lean_dec_ref(x_594);
 x_743 = lean_box(0);
}
if (lean_is_scalar(x_743)) {
 x_744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_744 = x_743;
}
lean_ctor_set(x_744, 0, x_741);
lean_ctor_set(x_744, 1, x_742);
return x_744;
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_dec(x_590);
lean_free_object(x_46);
lean_dec(x_52);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_745 = lean_ctor_get(x_591, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_591, 1);
lean_inc(x_746);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_747 = x_591;
} else {
 lean_dec_ref(x_591);
 x_747 = lean_box(0);
}
if (lean_is_scalar(x_747)) {
 x_748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_748 = x_747;
}
lean_ctor_set(x_748, 0, x_745);
lean_ctor_set(x_748, 1, x_746);
return x_748;
}
}
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_749 = lean_ctor_get(x_46, 0);
lean_inc(x_749);
lean_dec(x_46);
x_750 = lean_ctor_get(x_47, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_751 = x_47;
} else {
 lean_dec_ref(x_47);
 x_751 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_752 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_26, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
lean_dec(x_752);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_749);
x_755 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_749, x_5, x_6, x_7, x_8, x_754);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_758 = lean_infer_type(x_29, x_5, x_6, x_7, x_8, x_757);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_761 = lean_infer_type(x_30, x_5, x_6, x_7, x_8, x_760);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
lean_dec(x_761);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_750);
x_764 = lean_infer_type(x_750, x_5, x_6, x_7, x_8, x_763);
if (lean_obj_tag(x_764) == 0)
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_765 = lean_ctor_get(x_764, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_764, 1);
lean_inc(x_766);
lean_dec(x_764);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_759);
x_767 = l_Lean_Meta_getLevel(x_759, x_5, x_6, x_7, x_8, x_766);
if (lean_obj_tag(x_767) == 0)
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_767, 1);
lean_inc(x_769);
lean_dec(x_767);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_762);
x_770 = l_Lean_Meta_getLevel(x_762, x_5, x_6, x_7, x_8, x_769);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_770, 1);
lean_inc(x_772);
lean_dec(x_770);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_765);
x_773 = l_Lean_Meta_getLevel(x_765, x_5, x_6, x_7, x_8, x_772);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
lean_dec(x_773);
x_776 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_775);
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_779 = x_776;
} else {
 lean_dec_ref(x_776);
 x_779 = lean_box(0);
}
lean_inc(x_777);
x_780 = l_Lean_Expr_sort___override(x_777);
lean_inc(x_765);
x_781 = l_Lean_mkArrow(x_765, x_780, x_7, x_8, x_778);
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_784 = x_781;
} else {
 lean_dec_ref(x_781);
 x_784 = lean_box(0);
}
lean_inc(x_759);
x_785 = l_Lean_mkArrow(x_759, x_782, x_7, x_8, x_783);
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_785, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_788 = x_785;
} else {
 lean_dec_ref(x_785);
 x_788 = lean_box(0);
}
lean_ctor_set(x_36, 0, x_786);
x_789 = lean_box(0);
x_790 = lean_box(0);
x_791 = lean_unbox(x_789);
lean_inc(x_5);
x_792 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_791, x_790, x_5, x_6, x_7, x_8, x_787);
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_795 = x_792;
} else {
 lean_dec_ref(x_792);
 x_795 = lean_box(0);
}
x_796 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_796);
x_797 = l_Lean_Name_mkStr1(x_796);
x_798 = lean_box(0);
if (lean_is_scalar(x_795)) {
 x_799 = lean_alloc_ctor(1, 2, 0);
} else {
 x_799 = x_795;
 lean_ctor_set_tag(x_799, 1);
}
lean_ctor_set(x_799, 0, x_774);
lean_ctor_set(x_799, 1, x_798);
if (lean_is_scalar(x_788)) {
 x_800 = lean_alloc_ctor(1, 2, 0);
} else {
 x_800 = x_788;
 lean_ctor_set_tag(x_800, 1);
}
lean_ctor_set(x_800, 0, x_771);
lean_ctor_set(x_800, 1, x_799);
if (lean_is_scalar(x_784)) {
 x_801 = lean_alloc_ctor(1, 2, 0);
} else {
 x_801 = x_784;
 lean_ctor_set_tag(x_801, 1);
}
lean_ctor_set(x_801, 0, x_768);
lean_ctor_set(x_801, 1, x_800);
if (lean_is_scalar(x_779)) {
 x_802 = lean_alloc_ctor(1, 2, 0);
} else {
 x_802 = x_779;
 lean_ctor_set_tag(x_802, 1);
}
lean_ctor_set(x_802, 0, x_777);
lean_ctor_set(x_802, 1, x_801);
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_756);
lean_ctor_set(x_803, 1, x_802);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_803);
lean_ctor_set(x_35, 0, x_753);
lean_inc(x_35);
x_804 = l_Lean_Expr_const___override(x_797, x_35);
x_805 = lean_unsigned_to_nat(6u);
x_806 = lean_mk_empty_array_with_capacity(x_805);
lean_inc(x_759);
x_807 = lean_array_push(x_806, x_759);
lean_inc(x_762);
x_808 = lean_array_push(x_807, x_762);
lean_inc(x_765);
x_809 = lean_array_push(x_808, x_765);
lean_inc(x_26);
x_810 = lean_array_push(x_809, x_26);
lean_inc(x_749);
x_811 = lean_array_push(x_810, x_749);
lean_inc(x_793);
x_812 = lean_array_push(x_811, x_793);
x_813 = l_Lean_mkAppN(x_804, x_812);
lean_dec(x_812);
x_814 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_813);
x_815 = l_Lean_Meta_trySynthInstance(x_813, x_814, x_5, x_6, x_7, x_8, x_794);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
if (lean_obj_tag(x_816) == 1)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_813);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec(x_815);
x_818 = lean_ctor_get(x_816, 0);
lean_inc(x_818);
lean_dec(x_816);
x_819 = lean_mk_string_unchecked("trans", 5, 5);
x_820 = l_Lean_Name_mkStr2(x_796, x_819);
x_821 = l_Lean_Expr_const___override(x_820, x_35);
x_822 = lean_unsigned_to_nat(12u);
x_823 = lean_mk_empty_array_with_capacity(x_822);
x_824 = lean_array_push(x_823, x_759);
x_825 = lean_array_push(x_824, x_762);
x_826 = lean_array_push(x_825, x_765);
x_827 = lean_array_push(x_826, x_26);
x_828 = lean_array_push(x_827, x_749);
x_829 = lean_array_push(x_828, x_793);
x_830 = lean_array_push(x_829, x_818);
x_831 = lean_array_push(x_830, x_29);
x_832 = lean_array_push(x_831, x_30);
x_833 = lean_array_push(x_832, x_750);
x_834 = lean_array_push(x_833, x_1);
x_835 = lean_array_push(x_834, x_3);
x_836 = l_Lean_mkAppN(x_821, x_835);
lean_dec(x_835);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_836);
x_837 = lean_infer_type(x_836, x_5, x_6, x_7, x_8, x_817);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_837, 1);
lean_inc(x_839);
lean_dec(x_837);
x_840 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_838, x_6, x_839);
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
if (lean_is_exclusive(x_840)) {
 lean_ctor_release(x_840, 0);
 lean_ctor_release(x_840, 1);
 x_843 = x_840;
} else {
 lean_dec_ref(x_840);
 x_843 = lean_box(0);
}
x_844 = l_Lean_Expr_headBeta(x_841);
x_845 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_844, x_842);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
if (lean_obj_tag(x_846) == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec(x_836);
lean_dec(x_751);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_849 = l_Lean_stringToMessageData(x_848);
lean_dec(x_848);
x_850 = l_Lean_indentExpr(x_844);
if (lean_is_scalar(x_843)) {
 x_851 = lean_alloc_ctor(7, 2, 0);
} else {
 x_851 = x_843;
 lean_ctor_set_tag(x_851, 7);
}
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
x_852 = lean_mk_string_unchecked("", 0, 0);
x_853 = l_Lean_stringToMessageData(x_852);
lean_dec(x_852);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_853);
lean_ctor_set(x_31, 0, x_851);
x_854 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_847);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_857 = x_854;
} else {
 lean_dec_ref(x_854);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_855);
lean_ctor_set(x_858, 1, x_856);
return x_858;
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_846);
lean_dec(x_843);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_859 = lean_ctor_get(x_845, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_860 = x_845;
} else {
 lean_dec_ref(x_845);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_861 = x_751;
}
lean_ctor_set(x_861, 0, x_836);
lean_ctor_set(x_861, 1, x_844);
if (lean_is_scalar(x_860)) {
 x_862 = lean_alloc_ctor(0, 2, 0);
} else {
 x_862 = x_860;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_859);
return x_862;
}
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_836);
lean_dec(x_751);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_863 = lean_ctor_get(x_837, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_837, 1);
lean_inc(x_864);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_865 = x_837;
} else {
 lean_dec_ref(x_837);
 x_865 = lean_box(0);
}
if (lean_is_scalar(x_865)) {
 x_866 = lean_alloc_ctor(1, 2, 0);
} else {
 x_866 = x_865;
}
lean_ctor_set(x_866, 0, x_863);
lean_ctor_set(x_866, 1, x_864);
return x_866;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
lean_dec(x_816);
lean_dec(x_35);
lean_dec(x_796);
lean_dec(x_793);
lean_dec(x_765);
lean_dec(x_762);
lean_dec(x_759);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_867 = lean_ctor_get(x_815, 1);
lean_inc(x_867);
lean_dec(x_815);
x_868 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_869 = l_Lean_stringToMessageData(x_868);
lean_dec(x_868);
x_870 = l_Lean_indentExpr(x_813);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_870);
lean_ctor_set(x_31, 0, x_869);
x_871 = lean_mk_string_unchecked("", 0, 0);
x_872 = l_Lean_stringToMessageData(x_871);
lean_dec(x_871);
lean_inc(x_872);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_872);
lean_ctor_set(x_21, 0, x_31);
x_873 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_873);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_872);
lean_ctor_set(x_10, 0, x_20);
x_874 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_867);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_874;
}
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; 
lean_dec(x_813);
lean_dec(x_35);
lean_dec(x_796);
lean_dec(x_793);
lean_dec(x_765);
lean_dec(x_762);
lean_dec(x_759);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_875 = lean_ctor_get(x_815, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_815, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_815)) {
 lean_ctor_release(x_815, 0);
 lean_ctor_release(x_815, 1);
 x_877 = x_815;
} else {
 lean_dec_ref(x_815);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(1, 2, 0);
} else {
 x_878 = x_877;
}
lean_ctor_set(x_878, 0, x_875);
lean_ctor_set(x_878, 1, x_876);
return x_878;
}
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_771);
lean_dec(x_768);
lean_dec(x_765);
lean_dec(x_762);
lean_dec(x_759);
lean_dec(x_756);
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_879 = lean_ctor_get(x_773, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_773, 1);
lean_inc(x_880);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_881 = x_773;
} else {
 lean_dec_ref(x_773);
 x_881 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_882 = lean_alloc_ctor(1, 2, 0);
} else {
 x_882 = x_881;
}
lean_ctor_set(x_882, 0, x_879);
lean_ctor_set(x_882, 1, x_880);
return x_882;
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_768);
lean_dec(x_765);
lean_dec(x_762);
lean_dec(x_759);
lean_dec(x_756);
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_883 = lean_ctor_get(x_770, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_770, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 lean_ctor_release(x_770, 1);
 x_885 = x_770;
} else {
 lean_dec_ref(x_770);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_765);
lean_dec(x_762);
lean_dec(x_759);
lean_dec(x_756);
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_887 = lean_ctor_get(x_767, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_767, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_767)) {
 lean_ctor_release(x_767, 0);
 lean_ctor_release(x_767, 1);
 x_889 = x_767;
} else {
 lean_dec_ref(x_767);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
lean_dec(x_762);
lean_dec(x_759);
lean_dec(x_756);
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_891 = lean_ctor_get(x_764, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_764, 1);
lean_inc(x_892);
if (lean_is_exclusive(x_764)) {
 lean_ctor_release(x_764, 0);
 lean_ctor_release(x_764, 1);
 x_893 = x_764;
} else {
 lean_dec_ref(x_764);
 x_893 = lean_box(0);
}
if (lean_is_scalar(x_893)) {
 x_894 = lean_alloc_ctor(1, 2, 0);
} else {
 x_894 = x_893;
}
lean_ctor_set(x_894, 0, x_891);
lean_ctor_set(x_894, 1, x_892);
return x_894;
}
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_759);
lean_dec(x_756);
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_895 = lean_ctor_get(x_761, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_761, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_897 = x_761;
} else {
 lean_dec_ref(x_761);
 x_897 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_898 = lean_alloc_ctor(1, 2, 0);
} else {
 x_898 = x_897;
}
lean_ctor_set(x_898, 0, x_895);
lean_ctor_set(x_898, 1, x_896);
return x_898;
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_756);
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_899 = lean_ctor_get(x_758, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_758, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_901 = x_758;
} else {
 lean_dec_ref(x_758);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(1, 2, 0);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_899);
lean_ctor_set(x_902, 1, x_900);
return x_902;
}
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_903 = lean_ctor_get(x_755, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_755, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_905 = x_755;
} else {
 lean_dec_ref(x_755);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_905)) {
 x_906 = lean_alloc_ctor(1, 2, 0);
} else {
 x_906 = x_905;
}
lean_ctor_set(x_906, 0, x_903);
lean_ctor_set(x_906, 1, x_904);
return x_906;
}
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_749);
lean_free_object(x_35);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_907 = lean_ctor_get(x_752, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_752, 1);
lean_inc(x_908);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_909 = x_752;
} else {
 lean_dec_ref(x_752);
 x_909 = lean_box(0);
}
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_907);
lean_ctor_set(x_910, 1, x_908);
return x_910;
}
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_911 = lean_ctor_get(x_35, 1);
lean_inc(x_911);
lean_dec(x_35);
x_912 = lean_ctor_get(x_46, 0);
lean_inc(x_912);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_913 = x_46;
} else {
 lean_dec_ref(x_46);
 x_913 = lean_box(0);
}
x_914 = lean_ctor_get(x_47, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_915 = x_47;
} else {
 lean_dec_ref(x_47);
 x_915 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_916 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_26, x_5, x_6, x_7, x_8, x_911);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
lean_dec(x_916);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_912);
x_919 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_912, x_5, x_6, x_7, x_8, x_918);
if (lean_obj_tag(x_919) == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 1);
lean_inc(x_921);
lean_dec(x_919);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_922 = lean_infer_type(x_29, x_5, x_6, x_7, x_8, x_921);
if (lean_obj_tag(x_922) == 0)
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
x_923 = lean_ctor_get(x_922, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_922, 1);
lean_inc(x_924);
lean_dec(x_922);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_925 = lean_infer_type(x_30, x_5, x_6, x_7, x_8, x_924);
if (lean_obj_tag(x_925) == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; 
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
lean_dec(x_925);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_914);
x_928 = lean_infer_type(x_914, x_5, x_6, x_7, x_8, x_927);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
lean_dec(x_928);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_923);
x_931 = l_Lean_Meta_getLevel(x_923, x_5, x_6, x_7, x_8, x_930);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_931, 1);
lean_inc(x_933);
lean_dec(x_931);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_926);
x_934 = l_Lean_Meta_getLevel(x_926, x_5, x_6, x_7, x_8, x_933);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_934, 1);
lean_inc(x_936);
lean_dec(x_934);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_929);
x_937 = l_Lean_Meta_getLevel(x_929, x_5, x_6, x_7, x_8, x_936);
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; uint8_t x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_937, 1);
lean_inc(x_939);
lean_dec(x_937);
x_940 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_939);
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 x_943 = x_940;
} else {
 lean_dec_ref(x_940);
 x_943 = lean_box(0);
}
lean_inc(x_941);
x_944 = l_Lean_Expr_sort___override(x_941);
lean_inc(x_929);
x_945 = l_Lean_mkArrow(x_929, x_944, x_7, x_8, x_942);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_948 = x_945;
} else {
 lean_dec_ref(x_945);
 x_948 = lean_box(0);
}
lean_inc(x_923);
x_949 = l_Lean_mkArrow(x_923, x_946, x_7, x_8, x_947);
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_949, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 lean_ctor_release(x_949, 1);
 x_952 = x_949;
} else {
 lean_dec_ref(x_949);
 x_952 = lean_box(0);
}
lean_ctor_set(x_36, 0, x_950);
x_953 = lean_box(0);
x_954 = lean_box(0);
x_955 = lean_unbox(x_953);
lean_inc(x_5);
x_956 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_955, x_954, x_5, x_6, x_7, x_8, x_951);
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_959 = x_956;
} else {
 lean_dec_ref(x_956);
 x_959 = lean_box(0);
}
x_960 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_960);
x_961 = l_Lean_Name_mkStr1(x_960);
x_962 = lean_box(0);
if (lean_is_scalar(x_959)) {
 x_963 = lean_alloc_ctor(1, 2, 0);
} else {
 x_963 = x_959;
 lean_ctor_set_tag(x_963, 1);
}
lean_ctor_set(x_963, 0, x_938);
lean_ctor_set(x_963, 1, x_962);
if (lean_is_scalar(x_952)) {
 x_964 = lean_alloc_ctor(1, 2, 0);
} else {
 x_964 = x_952;
 lean_ctor_set_tag(x_964, 1);
}
lean_ctor_set(x_964, 0, x_935);
lean_ctor_set(x_964, 1, x_963);
if (lean_is_scalar(x_948)) {
 x_965 = lean_alloc_ctor(1, 2, 0);
} else {
 x_965 = x_948;
 lean_ctor_set_tag(x_965, 1);
}
lean_ctor_set(x_965, 0, x_932);
lean_ctor_set(x_965, 1, x_964);
if (lean_is_scalar(x_943)) {
 x_966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_966 = x_943;
 lean_ctor_set_tag(x_966, 1);
}
lean_ctor_set(x_966, 0, x_941);
lean_ctor_set(x_966, 1, x_965);
if (lean_is_scalar(x_913)) {
 x_967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_967 = x_913;
 lean_ctor_set_tag(x_967, 1);
}
lean_ctor_set(x_967, 0, x_920);
lean_ctor_set(x_967, 1, x_966);
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_917);
lean_ctor_set(x_968, 1, x_967);
lean_inc(x_968);
x_969 = l_Lean_Expr_const___override(x_961, x_968);
x_970 = lean_unsigned_to_nat(6u);
x_971 = lean_mk_empty_array_with_capacity(x_970);
lean_inc(x_923);
x_972 = lean_array_push(x_971, x_923);
lean_inc(x_926);
x_973 = lean_array_push(x_972, x_926);
lean_inc(x_929);
x_974 = lean_array_push(x_973, x_929);
lean_inc(x_26);
x_975 = lean_array_push(x_974, x_26);
lean_inc(x_912);
x_976 = lean_array_push(x_975, x_912);
lean_inc(x_957);
x_977 = lean_array_push(x_976, x_957);
x_978 = l_Lean_mkAppN(x_969, x_977);
lean_dec(x_977);
x_979 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_978);
x_980 = l_Lean_Meta_trySynthInstance(x_978, x_979, x_5, x_6, x_7, x_8, x_958);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
if (lean_obj_tag(x_981) == 1)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_978);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_982 = lean_ctor_get(x_980, 1);
lean_inc(x_982);
lean_dec(x_980);
x_983 = lean_ctor_get(x_981, 0);
lean_inc(x_983);
lean_dec(x_981);
x_984 = lean_mk_string_unchecked("trans", 5, 5);
x_985 = l_Lean_Name_mkStr2(x_960, x_984);
x_986 = l_Lean_Expr_const___override(x_985, x_968);
x_987 = lean_unsigned_to_nat(12u);
x_988 = lean_mk_empty_array_with_capacity(x_987);
x_989 = lean_array_push(x_988, x_923);
x_990 = lean_array_push(x_989, x_926);
x_991 = lean_array_push(x_990, x_929);
x_992 = lean_array_push(x_991, x_26);
x_993 = lean_array_push(x_992, x_912);
x_994 = lean_array_push(x_993, x_957);
x_995 = lean_array_push(x_994, x_983);
x_996 = lean_array_push(x_995, x_29);
x_997 = lean_array_push(x_996, x_30);
x_998 = lean_array_push(x_997, x_914);
x_999 = lean_array_push(x_998, x_1);
x_1000 = lean_array_push(x_999, x_3);
x_1001 = l_Lean_mkAppN(x_986, x_1000);
lean_dec(x_1000);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1001);
x_1002 = lean_infer_type(x_1001, x_5, x_6, x_7, x_8, x_982);
if (lean_obj_tag(x_1002) == 0)
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1003 = lean_ctor_get(x_1002, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_1002, 1);
lean_inc(x_1004);
lean_dec(x_1002);
x_1005 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1003, x_6, x_1004);
x_1006 = lean_ctor_get(x_1005, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1005, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 lean_ctor_release(x_1005, 1);
 x_1008 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1008 = lean_box(0);
}
x_1009 = l_Lean_Expr_headBeta(x_1006);
x_1010 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1009, x_1007);
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_1001);
lean_dec(x_915);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
lean_dec(x_1010);
x_1013 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_1014 = l_Lean_stringToMessageData(x_1013);
lean_dec(x_1013);
x_1015 = l_Lean_indentExpr(x_1009);
if (lean_is_scalar(x_1008)) {
 x_1016 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1016 = x_1008;
 lean_ctor_set_tag(x_1016, 7);
}
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
x_1017 = lean_mk_string_unchecked("", 0, 0);
x_1018 = l_Lean_stringToMessageData(x_1017);
lean_dec(x_1017);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_1018);
lean_ctor_set(x_31, 0, x_1016);
x_1019 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_1012);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1019, 1);
lean_inc(x_1021);
if (lean_is_exclusive(x_1019)) {
 lean_ctor_release(x_1019, 0);
 lean_ctor_release(x_1019, 1);
 x_1022 = x_1019;
} else {
 lean_dec_ref(x_1019);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1020);
lean_ctor_set(x_1023, 1, x_1021);
return x_1023;
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_1011);
lean_dec(x_1008);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1024 = lean_ctor_get(x_1010, 1);
lean_inc(x_1024);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1025 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1025 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_1026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1026 = x_915;
}
lean_ctor_set(x_1026, 0, x_1001);
lean_ctor_set(x_1026, 1, x_1009);
if (lean_is_scalar(x_1025)) {
 x_1027 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1027 = x_1025;
}
lean_ctor_set(x_1027, 0, x_1026);
lean_ctor_set(x_1027, 1, x_1024);
return x_1027;
}
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_1001);
lean_dec(x_915);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1028 = lean_ctor_get(x_1002, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1002, 1);
lean_inc(x_1029);
if (lean_is_exclusive(x_1002)) {
 lean_ctor_release(x_1002, 0);
 lean_ctor_release(x_1002, 1);
 x_1030 = x_1002;
} else {
 lean_dec_ref(x_1002);
 x_1030 = lean_box(0);
}
if (lean_is_scalar(x_1030)) {
 x_1031 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1031 = x_1030;
}
lean_ctor_set(x_1031, 0, x_1028);
lean_ctor_set(x_1031, 1, x_1029);
return x_1031;
}
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
lean_dec(x_981);
lean_dec(x_968);
lean_dec(x_960);
lean_dec(x_957);
lean_dec(x_929);
lean_dec(x_926);
lean_dec(x_923);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_912);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_1032 = lean_ctor_get(x_980, 1);
lean_inc(x_1032);
lean_dec(x_980);
x_1033 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_1034 = l_Lean_stringToMessageData(x_1033);
lean_dec(x_1033);
x_1035 = l_Lean_indentExpr(x_978);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_1035);
lean_ctor_set(x_31, 0, x_1034);
x_1036 = lean_mk_string_unchecked("", 0, 0);
x_1037 = l_Lean_stringToMessageData(x_1036);
lean_dec(x_1036);
lean_inc(x_1037);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_1037);
lean_ctor_set(x_21, 0, x_31);
x_1038 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_1038);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_1037);
lean_ctor_set(x_10, 0, x_20);
x_1039 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_1032);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1039;
}
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_978);
lean_dec(x_968);
lean_dec(x_960);
lean_dec(x_957);
lean_dec(x_929);
lean_dec(x_926);
lean_dec(x_923);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_912);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1040 = lean_ctor_get(x_980, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_980, 1);
lean_inc(x_1041);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_1042 = x_980;
} else {
 lean_dec_ref(x_980);
 x_1042 = lean_box(0);
}
if (lean_is_scalar(x_1042)) {
 x_1043 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1043 = x_1042;
}
lean_ctor_set(x_1043, 0, x_1040);
lean_ctor_set(x_1043, 1, x_1041);
return x_1043;
}
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_935);
lean_dec(x_932);
lean_dec(x_929);
lean_dec(x_926);
lean_dec(x_923);
lean_dec(x_920);
lean_dec(x_917);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1044 = lean_ctor_get(x_937, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_937, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_937)) {
 lean_ctor_release(x_937, 0);
 lean_ctor_release(x_937, 1);
 x_1046 = x_937;
} else {
 lean_dec_ref(x_937);
 x_1046 = lean_box(0);
}
if (lean_is_scalar(x_1046)) {
 x_1047 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1047 = x_1046;
}
lean_ctor_set(x_1047, 0, x_1044);
lean_ctor_set(x_1047, 1, x_1045);
return x_1047;
}
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_932);
lean_dec(x_929);
lean_dec(x_926);
lean_dec(x_923);
lean_dec(x_920);
lean_dec(x_917);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1048 = lean_ctor_get(x_934, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_934, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_1050 = x_934;
} else {
 lean_dec_ref(x_934);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1048);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_929);
lean_dec(x_926);
lean_dec(x_923);
lean_dec(x_920);
lean_dec(x_917);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1052 = lean_ctor_get(x_931, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_931, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_1054 = x_931;
} else {
 lean_dec_ref(x_931);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_1052);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
lean_dec(x_926);
lean_dec(x_923);
lean_dec(x_920);
lean_dec(x_917);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1056 = lean_ctor_get(x_928, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_928, 1);
lean_inc(x_1057);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_1058 = x_928;
} else {
 lean_dec_ref(x_928);
 x_1058 = lean_box(0);
}
if (lean_is_scalar(x_1058)) {
 x_1059 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1059 = x_1058;
}
lean_ctor_set(x_1059, 0, x_1056);
lean_ctor_set(x_1059, 1, x_1057);
return x_1059;
}
}
else
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
lean_dec(x_923);
lean_dec(x_920);
lean_dec(x_917);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1060 = lean_ctor_get(x_925, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_925, 1);
lean_inc(x_1061);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 lean_ctor_release(x_925, 1);
 x_1062 = x_925;
} else {
 lean_dec_ref(x_925);
 x_1062 = lean_box(0);
}
if (lean_is_scalar(x_1062)) {
 x_1063 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1063 = x_1062;
}
lean_ctor_set(x_1063, 0, x_1060);
lean_ctor_set(x_1063, 1, x_1061);
return x_1063;
}
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_920);
lean_dec(x_917);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1064 = lean_ctor_get(x_922, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_922, 1);
lean_inc(x_1065);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 x_1066 = x_922;
} else {
 lean_dec_ref(x_922);
 x_1066 = lean_box(0);
}
if (lean_is_scalar(x_1066)) {
 x_1067 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1067 = x_1066;
}
lean_ctor_set(x_1067, 0, x_1064);
lean_ctor_set(x_1067, 1, x_1065);
return x_1067;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_917);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1068 = lean_ctor_get(x_919, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_919, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 lean_ctor_release(x_919, 1);
 x_1070 = x_919;
} else {
 lean_dec_ref(x_919);
 x_1070 = lean_box(0);
}
if (lean_is_scalar(x_1070)) {
 x_1071 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1071 = x_1070;
}
lean_ctor_set(x_1071, 0, x_1068);
lean_ctor_set(x_1071, 1, x_1069);
return x_1071;
}
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_free_object(x_36);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1072 = lean_ctor_get(x_916, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_916, 1);
lean_inc(x_1073);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_1074 = x_916;
} else {
 lean_dec_ref(x_916);
 x_1074 = lean_box(0);
}
if (lean_is_scalar(x_1074)) {
 x_1075 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1075 = x_1074;
}
lean_ctor_set(x_1075, 0, x_1072);
lean_ctor_set(x_1075, 1, x_1073);
return x_1075;
}
}
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1076 = lean_ctor_get(x_36, 0);
lean_inc(x_1076);
lean_dec(x_36);
x_1077 = lean_ctor_get(x_1076, 1);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_35, 1);
lean_inc(x_1078);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_1079 = x_35;
} else {
 lean_dec_ref(x_35);
 x_1079 = lean_box(0);
}
x_1080 = lean_ctor_get(x_1076, 0);
lean_inc(x_1080);
if (lean_is_exclusive(x_1076)) {
 lean_ctor_release(x_1076, 0);
 lean_ctor_release(x_1076, 1);
 x_1081 = x_1076;
} else {
 lean_dec_ref(x_1076);
 x_1081 = lean_box(0);
}
x_1082 = lean_ctor_get(x_1077, 1);
lean_inc(x_1082);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1083 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1083 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_1084 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_26, x_5, x_6, x_7, x_8, x_1078);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
lean_dec(x_1084);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1080);
x_1087 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1080, x_5, x_6, x_7, x_8, x_1086);
if (lean_obj_tag(x_1087) == 0)
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
x_1088 = lean_ctor_get(x_1087, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1087, 1);
lean_inc(x_1089);
lean_dec(x_1087);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_1090 = lean_infer_type(x_29, x_5, x_6, x_7, x_8, x_1089);
if (lean_obj_tag(x_1090) == 0)
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1091 = lean_ctor_get(x_1090, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1090, 1);
lean_inc(x_1092);
lean_dec(x_1090);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_1093 = lean_infer_type(x_30, x_5, x_6, x_7, x_8, x_1092);
if (lean_obj_tag(x_1093) == 0)
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1094 = lean_ctor_get(x_1093, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1093, 1);
lean_inc(x_1095);
lean_dec(x_1093);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1082);
x_1096 = lean_infer_type(x_1082, x_5, x_6, x_7, x_8, x_1095);
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1097 = lean_ctor_get(x_1096, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1096, 1);
lean_inc(x_1098);
lean_dec(x_1096);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1091);
x_1099 = l_Lean_Meta_getLevel(x_1091, x_5, x_6, x_7, x_8, x_1098);
if (lean_obj_tag(x_1099) == 0)
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1100 = lean_ctor_get(x_1099, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1099, 1);
lean_inc(x_1101);
lean_dec(x_1099);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1094);
x_1102 = l_Lean_Meta_getLevel(x_1094, x_5, x_6, x_7, x_8, x_1101);
if (lean_obj_tag(x_1102) == 0)
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1103 = lean_ctor_get(x_1102, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1102, 1);
lean_inc(x_1104);
lean_dec(x_1102);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1097);
x_1105 = l_Lean_Meta_getLevel(x_1097, x_5, x_6, x_7, x_8, x_1104);
if (lean_obj_tag(x_1105) == 0)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; uint8_t x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
x_1106 = lean_ctor_get(x_1105, 0);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_1105, 1);
lean_inc(x_1107);
lean_dec(x_1105);
x_1108 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1107);
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
if (lean_is_exclusive(x_1108)) {
 lean_ctor_release(x_1108, 0);
 lean_ctor_release(x_1108, 1);
 x_1111 = x_1108;
} else {
 lean_dec_ref(x_1108);
 x_1111 = lean_box(0);
}
lean_inc(x_1109);
x_1112 = l_Lean_Expr_sort___override(x_1109);
lean_inc(x_1097);
x_1113 = l_Lean_mkArrow(x_1097, x_1112, x_7, x_8, x_1110);
x_1114 = lean_ctor_get(x_1113, 0);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1113, 1);
lean_inc(x_1115);
if (lean_is_exclusive(x_1113)) {
 lean_ctor_release(x_1113, 0);
 lean_ctor_release(x_1113, 1);
 x_1116 = x_1113;
} else {
 lean_dec_ref(x_1113);
 x_1116 = lean_box(0);
}
lean_inc(x_1091);
x_1117 = l_Lean_mkArrow(x_1091, x_1114, x_7, x_8, x_1115);
x_1118 = lean_ctor_get(x_1117, 0);
lean_inc(x_1118);
x_1119 = lean_ctor_get(x_1117, 1);
lean_inc(x_1119);
if (lean_is_exclusive(x_1117)) {
 lean_ctor_release(x_1117, 0);
 lean_ctor_release(x_1117, 1);
 x_1120 = x_1117;
} else {
 lean_dec_ref(x_1117);
 x_1120 = lean_box(0);
}
x_1121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1121, 0, x_1118);
x_1122 = lean_box(0);
x_1123 = lean_box(0);
x_1124 = lean_unbox(x_1122);
lean_inc(x_5);
x_1125 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1121, x_1124, x_1123, x_5, x_6, x_7, x_8, x_1119);
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
x_1127 = lean_ctor_get(x_1125, 1);
lean_inc(x_1127);
if (lean_is_exclusive(x_1125)) {
 lean_ctor_release(x_1125, 0);
 lean_ctor_release(x_1125, 1);
 x_1128 = x_1125;
} else {
 lean_dec_ref(x_1125);
 x_1128 = lean_box(0);
}
x_1129 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_1129);
x_1130 = l_Lean_Name_mkStr1(x_1129);
x_1131 = lean_box(0);
if (lean_is_scalar(x_1128)) {
 x_1132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1132 = x_1128;
 lean_ctor_set_tag(x_1132, 1);
}
lean_ctor_set(x_1132, 0, x_1106);
lean_ctor_set(x_1132, 1, x_1131);
if (lean_is_scalar(x_1120)) {
 x_1133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1133 = x_1120;
 lean_ctor_set_tag(x_1133, 1);
}
lean_ctor_set(x_1133, 0, x_1103);
lean_ctor_set(x_1133, 1, x_1132);
if (lean_is_scalar(x_1116)) {
 x_1134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1134 = x_1116;
 lean_ctor_set_tag(x_1134, 1);
}
lean_ctor_set(x_1134, 0, x_1100);
lean_ctor_set(x_1134, 1, x_1133);
if (lean_is_scalar(x_1111)) {
 x_1135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1135 = x_1111;
 lean_ctor_set_tag(x_1135, 1);
}
lean_ctor_set(x_1135, 0, x_1109);
lean_ctor_set(x_1135, 1, x_1134);
if (lean_is_scalar(x_1081)) {
 x_1136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1136 = x_1081;
 lean_ctor_set_tag(x_1136, 1);
}
lean_ctor_set(x_1136, 0, x_1088);
lean_ctor_set(x_1136, 1, x_1135);
if (lean_is_scalar(x_1079)) {
 x_1137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1137 = x_1079;
 lean_ctor_set_tag(x_1137, 1);
}
lean_ctor_set(x_1137, 0, x_1085);
lean_ctor_set(x_1137, 1, x_1136);
lean_inc(x_1137);
x_1138 = l_Lean_Expr_const___override(x_1130, x_1137);
x_1139 = lean_unsigned_to_nat(6u);
x_1140 = lean_mk_empty_array_with_capacity(x_1139);
lean_inc(x_1091);
x_1141 = lean_array_push(x_1140, x_1091);
lean_inc(x_1094);
x_1142 = lean_array_push(x_1141, x_1094);
lean_inc(x_1097);
x_1143 = lean_array_push(x_1142, x_1097);
lean_inc(x_26);
x_1144 = lean_array_push(x_1143, x_26);
lean_inc(x_1080);
x_1145 = lean_array_push(x_1144, x_1080);
lean_inc(x_1126);
x_1146 = lean_array_push(x_1145, x_1126);
x_1147 = l_Lean_mkAppN(x_1138, x_1146);
lean_dec(x_1146);
x_1148 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1147);
x_1149 = l_Lean_Meta_trySynthInstance(x_1147, x_1148, x_5, x_6, x_7, x_8, x_1127);
if (lean_obj_tag(x_1149) == 0)
{
lean_object* x_1150; 
x_1150 = lean_ctor_get(x_1149, 0);
lean_inc(x_1150);
if (lean_obj_tag(x_1150) == 1)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
lean_dec(x_1147);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_1151 = lean_ctor_get(x_1149, 1);
lean_inc(x_1151);
lean_dec(x_1149);
x_1152 = lean_ctor_get(x_1150, 0);
lean_inc(x_1152);
lean_dec(x_1150);
x_1153 = lean_mk_string_unchecked("trans", 5, 5);
x_1154 = l_Lean_Name_mkStr2(x_1129, x_1153);
x_1155 = l_Lean_Expr_const___override(x_1154, x_1137);
x_1156 = lean_unsigned_to_nat(12u);
x_1157 = lean_mk_empty_array_with_capacity(x_1156);
x_1158 = lean_array_push(x_1157, x_1091);
x_1159 = lean_array_push(x_1158, x_1094);
x_1160 = lean_array_push(x_1159, x_1097);
x_1161 = lean_array_push(x_1160, x_26);
x_1162 = lean_array_push(x_1161, x_1080);
x_1163 = lean_array_push(x_1162, x_1126);
x_1164 = lean_array_push(x_1163, x_1152);
x_1165 = lean_array_push(x_1164, x_29);
x_1166 = lean_array_push(x_1165, x_30);
x_1167 = lean_array_push(x_1166, x_1082);
x_1168 = lean_array_push(x_1167, x_1);
x_1169 = lean_array_push(x_1168, x_3);
x_1170 = l_Lean_mkAppN(x_1155, x_1169);
lean_dec(x_1169);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1170);
x_1171 = lean_infer_type(x_1170, x_5, x_6, x_7, x_8, x_1151);
if (lean_obj_tag(x_1171) == 0)
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
x_1172 = lean_ctor_get(x_1171, 0);
lean_inc(x_1172);
x_1173 = lean_ctor_get(x_1171, 1);
lean_inc(x_1173);
lean_dec(x_1171);
x_1174 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1172, x_6, x_1173);
x_1175 = lean_ctor_get(x_1174, 0);
lean_inc(x_1175);
x_1176 = lean_ctor_get(x_1174, 1);
lean_inc(x_1176);
if (lean_is_exclusive(x_1174)) {
 lean_ctor_release(x_1174, 0);
 lean_ctor_release(x_1174, 1);
 x_1177 = x_1174;
} else {
 lean_dec_ref(x_1174);
 x_1177 = lean_box(0);
}
x_1178 = l_Lean_Expr_headBeta(x_1175);
x_1179 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1178, x_1176);
x_1180 = lean_ctor_get(x_1179, 0);
lean_inc(x_1180);
if (lean_obj_tag(x_1180) == 0)
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
lean_dec(x_1170);
lean_dec(x_1083);
x_1181 = lean_ctor_get(x_1179, 1);
lean_inc(x_1181);
lean_dec(x_1179);
x_1182 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_1183 = l_Lean_stringToMessageData(x_1182);
lean_dec(x_1182);
x_1184 = l_Lean_indentExpr(x_1178);
if (lean_is_scalar(x_1177)) {
 x_1185 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1185 = x_1177;
 lean_ctor_set_tag(x_1185, 7);
}
lean_ctor_set(x_1185, 0, x_1183);
lean_ctor_set(x_1185, 1, x_1184);
x_1186 = lean_mk_string_unchecked("", 0, 0);
x_1187 = l_Lean_stringToMessageData(x_1186);
lean_dec(x_1186);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_1187);
lean_ctor_set(x_31, 0, x_1185);
x_1188 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_5, x_6, x_7, x_8, x_1181);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1189 = lean_ctor_get(x_1188, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1188, 1);
lean_inc(x_1190);
if (lean_is_exclusive(x_1188)) {
 lean_ctor_release(x_1188, 0);
 lean_ctor_release(x_1188, 1);
 x_1191 = x_1188;
} else {
 lean_dec_ref(x_1188);
 x_1191 = lean_box(0);
}
if (lean_is_scalar(x_1191)) {
 x_1192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1192 = x_1191;
}
lean_ctor_set(x_1192, 0, x_1189);
lean_ctor_set(x_1192, 1, x_1190);
return x_1192;
}
else
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
lean_dec(x_1180);
lean_dec(x_1177);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1193 = lean_ctor_get(x_1179, 1);
lean_inc(x_1193);
if (lean_is_exclusive(x_1179)) {
 lean_ctor_release(x_1179, 0);
 lean_ctor_release(x_1179, 1);
 x_1194 = x_1179;
} else {
 lean_dec_ref(x_1179);
 x_1194 = lean_box(0);
}
if (lean_is_scalar(x_1083)) {
 x_1195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1195 = x_1083;
}
lean_ctor_set(x_1195, 0, x_1170);
lean_ctor_set(x_1195, 1, x_1178);
if (lean_is_scalar(x_1194)) {
 x_1196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1196 = x_1194;
}
lean_ctor_set(x_1196, 0, x_1195);
lean_ctor_set(x_1196, 1, x_1193);
return x_1196;
}
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
lean_dec(x_1170);
lean_dec(x_1083);
lean_free_object(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1197 = lean_ctor_get(x_1171, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_1171, 1);
lean_inc(x_1198);
if (lean_is_exclusive(x_1171)) {
 lean_ctor_release(x_1171, 0);
 lean_ctor_release(x_1171, 1);
 x_1199 = x_1171;
} else {
 lean_dec_ref(x_1171);
 x_1199 = lean_box(0);
}
if (lean_is_scalar(x_1199)) {
 x_1200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1200 = x_1199;
}
lean_ctor_set(x_1200, 0, x_1197);
lean_ctor_set(x_1200, 1, x_1198);
return x_1200;
}
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_dec(x_1150);
lean_dec(x_1137);
lean_dec(x_1129);
lean_dec(x_1126);
lean_dec(x_1097);
lean_dec(x_1094);
lean_dec(x_1091);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1080);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_1201 = lean_ctor_get(x_1149, 1);
lean_inc(x_1201);
lean_dec(x_1149);
x_1202 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_1203 = l_Lean_stringToMessageData(x_1202);
lean_dec(x_1202);
x_1204 = l_Lean_indentExpr(x_1147);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_1204);
lean_ctor_set(x_31, 0, x_1203);
x_1205 = lean_mk_string_unchecked("", 0, 0);
x_1206 = l_Lean_stringToMessageData(x_1205);
lean_dec(x_1205);
lean_inc(x_1206);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_1206);
lean_ctor_set(x_21, 0, x_31);
x_1207 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_1207);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_1206);
lean_ctor_set(x_10, 0, x_20);
x_1208 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_1201);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1208;
}
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
lean_dec(x_1147);
lean_dec(x_1137);
lean_dec(x_1129);
lean_dec(x_1126);
lean_dec(x_1097);
lean_dec(x_1094);
lean_dec(x_1091);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1080);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1209 = lean_ctor_get(x_1149, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1149, 1);
lean_inc(x_1210);
if (lean_is_exclusive(x_1149)) {
 lean_ctor_release(x_1149, 0);
 lean_ctor_release(x_1149, 1);
 x_1211 = x_1149;
} else {
 lean_dec_ref(x_1149);
 x_1211 = lean_box(0);
}
if (lean_is_scalar(x_1211)) {
 x_1212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1212 = x_1211;
}
lean_ctor_set(x_1212, 0, x_1209);
lean_ctor_set(x_1212, 1, x_1210);
return x_1212;
}
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1103);
lean_dec(x_1100);
lean_dec(x_1097);
lean_dec(x_1094);
lean_dec(x_1091);
lean_dec(x_1088);
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1213 = lean_ctor_get(x_1105, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1105, 1);
lean_inc(x_1214);
if (lean_is_exclusive(x_1105)) {
 lean_ctor_release(x_1105, 0);
 lean_ctor_release(x_1105, 1);
 x_1215 = x_1105;
} else {
 lean_dec_ref(x_1105);
 x_1215 = lean_box(0);
}
if (lean_is_scalar(x_1215)) {
 x_1216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1216 = x_1215;
}
lean_ctor_set(x_1216, 0, x_1213);
lean_ctor_set(x_1216, 1, x_1214);
return x_1216;
}
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
lean_dec(x_1100);
lean_dec(x_1097);
lean_dec(x_1094);
lean_dec(x_1091);
lean_dec(x_1088);
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1217 = lean_ctor_get(x_1102, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1102, 1);
lean_inc(x_1218);
if (lean_is_exclusive(x_1102)) {
 lean_ctor_release(x_1102, 0);
 lean_ctor_release(x_1102, 1);
 x_1219 = x_1102;
} else {
 lean_dec_ref(x_1102);
 x_1219 = lean_box(0);
}
if (lean_is_scalar(x_1219)) {
 x_1220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1220 = x_1219;
}
lean_ctor_set(x_1220, 0, x_1217);
lean_ctor_set(x_1220, 1, x_1218);
return x_1220;
}
}
else
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
lean_dec(x_1097);
lean_dec(x_1094);
lean_dec(x_1091);
lean_dec(x_1088);
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1221 = lean_ctor_get(x_1099, 0);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1099, 1);
lean_inc(x_1222);
if (lean_is_exclusive(x_1099)) {
 lean_ctor_release(x_1099, 0);
 lean_ctor_release(x_1099, 1);
 x_1223 = x_1099;
} else {
 lean_dec_ref(x_1099);
 x_1223 = lean_box(0);
}
if (lean_is_scalar(x_1223)) {
 x_1224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1224 = x_1223;
}
lean_ctor_set(x_1224, 0, x_1221);
lean_ctor_set(x_1224, 1, x_1222);
return x_1224;
}
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1094);
lean_dec(x_1091);
lean_dec(x_1088);
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1225 = lean_ctor_get(x_1096, 0);
lean_inc(x_1225);
x_1226 = lean_ctor_get(x_1096, 1);
lean_inc(x_1226);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1227 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1227 = lean_box(0);
}
if (lean_is_scalar(x_1227)) {
 x_1228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1228 = x_1227;
}
lean_ctor_set(x_1228, 0, x_1225);
lean_ctor_set(x_1228, 1, x_1226);
return x_1228;
}
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
lean_dec(x_1091);
lean_dec(x_1088);
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1229 = lean_ctor_get(x_1093, 0);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_1093, 1);
lean_inc(x_1230);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 x_1231 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1231 = lean_box(0);
}
if (lean_is_scalar(x_1231)) {
 x_1232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1232 = x_1231;
}
lean_ctor_set(x_1232, 0, x_1229);
lean_ctor_set(x_1232, 1, x_1230);
return x_1232;
}
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
lean_dec(x_1088);
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1233 = lean_ctor_get(x_1090, 0);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1090, 1);
lean_inc(x_1234);
if (lean_is_exclusive(x_1090)) {
 lean_ctor_release(x_1090, 0);
 lean_ctor_release(x_1090, 1);
 x_1235 = x_1090;
} else {
 lean_dec_ref(x_1090);
 x_1235 = lean_box(0);
}
if (lean_is_scalar(x_1235)) {
 x_1236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1236 = x_1235;
}
lean_ctor_set(x_1236, 0, x_1233);
lean_ctor_set(x_1236, 1, x_1234);
return x_1236;
}
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
lean_dec(x_1085);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1237 = lean_ctor_get(x_1087, 0);
lean_inc(x_1237);
x_1238 = lean_ctor_get(x_1087, 1);
lean_inc(x_1238);
if (lean_is_exclusive(x_1087)) {
 lean_ctor_release(x_1087, 0);
 lean_ctor_release(x_1087, 1);
 x_1239 = x_1087;
} else {
 lean_dec_ref(x_1087);
 x_1239 = lean_box(0);
}
if (lean_is_scalar(x_1239)) {
 x_1240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1240 = x_1239;
}
lean_ctor_set(x_1240, 0, x_1237);
lean_ctor_set(x_1240, 1, x_1238);
return x_1240;
}
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1241 = lean_ctor_get(x_1084, 0);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1084, 1);
lean_inc(x_1242);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1243 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1243 = lean_box(0);
}
if (lean_is_scalar(x_1243)) {
 x_1244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1244 = x_1243;
}
lean_ctor_set(x_1244, 0, x_1241);
lean_ctor_set(x_1244, 1, x_1242);
return x_1244;
}
}
}
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1245 = lean_ctor_get(x_31, 0);
x_1246 = lean_ctor_get(x_31, 1);
lean_inc(x_1246);
lean_inc(x_1245);
lean_dec(x_31);
x_1247 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1245, x_1246);
lean_dec(x_1245);
x_1248 = lean_ctor_get(x_1247, 0);
lean_inc(x_1248);
if (lean_obj_tag(x_1248) == 0)
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_1249 = lean_ctor_get(x_1247, 1);
lean_inc(x_1249);
lean_dec(x_1247);
x_1250 = lean_mk_string_unchecked("Lean.Elab.Calc", 14, 14);
x_1251 = lean_mk_string_unchecked("Lean.Elab.Term.mkCalcTrans", 26, 26);
x_1252 = lean_unsigned_to_nat(31u);
x_1253 = lean_unsigned_to_nat(72u);
x_1254 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_1255 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1250, x_1251, x_1252, x_1253, x_1254);
lean_dec(x_1254);
lean_dec(x_1251);
lean_dec(x_1250);
x_1256 = l_panic___at___Lean_Elab_Term_mkCalcTrans_spec__0(x_1255, x_5, x_6, x_7, x_8, x_1249);
return x_1256;
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
x_1257 = lean_ctor_get(x_1248, 0);
lean_inc(x_1257);
if (lean_is_exclusive(x_1248)) {
 lean_ctor_release(x_1248, 0);
 x_1258 = x_1248;
} else {
 lean_dec_ref(x_1248);
 x_1258 = lean_box(0);
}
x_1259 = lean_ctor_get(x_1257, 1);
lean_inc(x_1259);
x_1260 = lean_ctor_get(x_1247, 1);
lean_inc(x_1260);
if (lean_is_exclusive(x_1247)) {
 lean_ctor_release(x_1247, 0);
 lean_ctor_release(x_1247, 1);
 x_1261 = x_1247;
} else {
 lean_dec_ref(x_1247);
 x_1261 = lean_box(0);
}
x_1262 = lean_ctor_get(x_1257, 0);
lean_inc(x_1262);
if (lean_is_exclusive(x_1257)) {
 lean_ctor_release(x_1257, 0);
 lean_ctor_release(x_1257, 1);
 x_1263 = x_1257;
} else {
 lean_dec_ref(x_1257);
 x_1263 = lean_box(0);
}
x_1264 = lean_ctor_get(x_1259, 1);
lean_inc(x_1264);
if (lean_is_exclusive(x_1259)) {
 lean_ctor_release(x_1259, 0);
 lean_ctor_release(x_1259, 1);
 x_1265 = x_1259;
} else {
 lean_dec_ref(x_1259);
 x_1265 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_1266 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_26, x_5, x_6, x_7, x_8, x_1260);
if (lean_obj_tag(x_1266) == 0)
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1266, 0);
lean_inc(x_1267);
x_1268 = lean_ctor_get(x_1266, 1);
lean_inc(x_1268);
lean_dec(x_1266);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1262);
x_1269 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1262, x_5, x_6, x_7, x_8, x_1268);
if (lean_obj_tag(x_1269) == 0)
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1270 = lean_ctor_get(x_1269, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1269, 1);
lean_inc(x_1271);
lean_dec(x_1269);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_1272 = lean_infer_type(x_29, x_5, x_6, x_7, x_8, x_1271);
if (lean_obj_tag(x_1272) == 0)
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
x_1273 = lean_ctor_get(x_1272, 0);
lean_inc(x_1273);
x_1274 = lean_ctor_get(x_1272, 1);
lean_inc(x_1274);
lean_dec(x_1272);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_30);
x_1275 = lean_infer_type(x_30, x_5, x_6, x_7, x_8, x_1274);
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1276 = lean_ctor_get(x_1275, 0);
lean_inc(x_1276);
x_1277 = lean_ctor_get(x_1275, 1);
lean_inc(x_1277);
lean_dec(x_1275);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1264);
x_1278 = lean_infer_type(x_1264, x_5, x_6, x_7, x_8, x_1277);
if (lean_obj_tag(x_1278) == 0)
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; 
x_1279 = lean_ctor_get(x_1278, 0);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_1278, 1);
lean_inc(x_1280);
lean_dec(x_1278);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1273);
x_1281 = l_Lean_Meta_getLevel(x_1273, x_5, x_6, x_7, x_8, x_1280);
if (lean_obj_tag(x_1281) == 0)
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1282 = lean_ctor_get(x_1281, 0);
lean_inc(x_1282);
x_1283 = lean_ctor_get(x_1281, 1);
lean_inc(x_1283);
lean_dec(x_1281);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1276);
x_1284 = l_Lean_Meta_getLevel(x_1276, x_5, x_6, x_7, x_8, x_1283);
if (lean_obj_tag(x_1284) == 0)
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1285 = lean_ctor_get(x_1284, 0);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1284, 1);
lean_inc(x_1286);
lean_dec(x_1284);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1279);
x_1287 = l_Lean_Meta_getLevel(x_1279, x_5, x_6, x_7, x_8, x_1286);
if (lean_obj_tag(x_1287) == 0)
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; uint8_t x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
x_1288 = lean_ctor_get(x_1287, 0);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1287, 1);
lean_inc(x_1289);
lean_dec(x_1287);
x_1290 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1289);
x_1291 = lean_ctor_get(x_1290, 0);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1290, 1);
lean_inc(x_1292);
if (lean_is_exclusive(x_1290)) {
 lean_ctor_release(x_1290, 0);
 lean_ctor_release(x_1290, 1);
 x_1293 = x_1290;
} else {
 lean_dec_ref(x_1290);
 x_1293 = lean_box(0);
}
lean_inc(x_1291);
x_1294 = l_Lean_Expr_sort___override(x_1291);
lean_inc(x_1279);
x_1295 = l_Lean_mkArrow(x_1279, x_1294, x_7, x_8, x_1292);
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1295, 1);
lean_inc(x_1297);
if (lean_is_exclusive(x_1295)) {
 lean_ctor_release(x_1295, 0);
 lean_ctor_release(x_1295, 1);
 x_1298 = x_1295;
} else {
 lean_dec_ref(x_1295);
 x_1298 = lean_box(0);
}
lean_inc(x_1273);
x_1299 = l_Lean_mkArrow(x_1273, x_1296, x_7, x_8, x_1297);
x_1300 = lean_ctor_get(x_1299, 0);
lean_inc(x_1300);
x_1301 = lean_ctor_get(x_1299, 1);
lean_inc(x_1301);
if (lean_is_exclusive(x_1299)) {
 lean_ctor_release(x_1299, 0);
 lean_ctor_release(x_1299, 1);
 x_1302 = x_1299;
} else {
 lean_dec_ref(x_1299);
 x_1302 = lean_box(0);
}
if (lean_is_scalar(x_1258)) {
 x_1303 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1303 = x_1258;
}
lean_ctor_set(x_1303, 0, x_1300);
x_1304 = lean_box(0);
x_1305 = lean_box(0);
x_1306 = lean_unbox(x_1304);
lean_inc(x_5);
x_1307 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1303, x_1306, x_1305, x_5, x_6, x_7, x_8, x_1301);
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1307, 1);
lean_inc(x_1309);
if (lean_is_exclusive(x_1307)) {
 lean_ctor_release(x_1307, 0);
 lean_ctor_release(x_1307, 1);
 x_1310 = x_1307;
} else {
 lean_dec_ref(x_1307);
 x_1310 = lean_box(0);
}
x_1311 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_1311);
x_1312 = l_Lean_Name_mkStr1(x_1311);
x_1313 = lean_box(0);
if (lean_is_scalar(x_1310)) {
 x_1314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1314 = x_1310;
 lean_ctor_set_tag(x_1314, 1);
}
lean_ctor_set(x_1314, 0, x_1288);
lean_ctor_set(x_1314, 1, x_1313);
if (lean_is_scalar(x_1302)) {
 x_1315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1315 = x_1302;
 lean_ctor_set_tag(x_1315, 1);
}
lean_ctor_set(x_1315, 0, x_1285);
lean_ctor_set(x_1315, 1, x_1314);
if (lean_is_scalar(x_1298)) {
 x_1316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1316 = x_1298;
 lean_ctor_set_tag(x_1316, 1);
}
lean_ctor_set(x_1316, 0, x_1282);
lean_ctor_set(x_1316, 1, x_1315);
if (lean_is_scalar(x_1293)) {
 x_1317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1317 = x_1293;
 lean_ctor_set_tag(x_1317, 1);
}
lean_ctor_set(x_1317, 0, x_1291);
lean_ctor_set(x_1317, 1, x_1316);
if (lean_is_scalar(x_1263)) {
 x_1318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1318 = x_1263;
 lean_ctor_set_tag(x_1318, 1);
}
lean_ctor_set(x_1318, 0, x_1270);
lean_ctor_set(x_1318, 1, x_1317);
if (lean_is_scalar(x_1261)) {
 x_1319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1319 = x_1261;
 lean_ctor_set_tag(x_1319, 1);
}
lean_ctor_set(x_1319, 0, x_1267);
lean_ctor_set(x_1319, 1, x_1318);
lean_inc(x_1319);
x_1320 = l_Lean_Expr_const___override(x_1312, x_1319);
x_1321 = lean_unsigned_to_nat(6u);
x_1322 = lean_mk_empty_array_with_capacity(x_1321);
lean_inc(x_1273);
x_1323 = lean_array_push(x_1322, x_1273);
lean_inc(x_1276);
x_1324 = lean_array_push(x_1323, x_1276);
lean_inc(x_1279);
x_1325 = lean_array_push(x_1324, x_1279);
lean_inc(x_26);
x_1326 = lean_array_push(x_1325, x_26);
lean_inc(x_1262);
x_1327 = lean_array_push(x_1326, x_1262);
lean_inc(x_1308);
x_1328 = lean_array_push(x_1327, x_1308);
x_1329 = l_Lean_mkAppN(x_1320, x_1328);
lean_dec(x_1328);
x_1330 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1329);
x_1331 = l_Lean_Meta_trySynthInstance(x_1329, x_1330, x_5, x_6, x_7, x_8, x_1309);
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1332; 
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
if (lean_obj_tag(x_1332) == 1)
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
lean_dec(x_1329);
lean_free_object(x_21);
lean_free_object(x_20);
lean_free_object(x_10);
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
lean_dec(x_1331);
x_1334 = lean_ctor_get(x_1332, 0);
lean_inc(x_1334);
lean_dec(x_1332);
x_1335 = lean_mk_string_unchecked("trans", 5, 5);
x_1336 = l_Lean_Name_mkStr2(x_1311, x_1335);
x_1337 = l_Lean_Expr_const___override(x_1336, x_1319);
x_1338 = lean_unsigned_to_nat(12u);
x_1339 = lean_mk_empty_array_with_capacity(x_1338);
x_1340 = lean_array_push(x_1339, x_1273);
x_1341 = lean_array_push(x_1340, x_1276);
x_1342 = lean_array_push(x_1341, x_1279);
x_1343 = lean_array_push(x_1342, x_26);
x_1344 = lean_array_push(x_1343, x_1262);
x_1345 = lean_array_push(x_1344, x_1308);
x_1346 = lean_array_push(x_1345, x_1334);
x_1347 = lean_array_push(x_1346, x_29);
x_1348 = lean_array_push(x_1347, x_30);
x_1349 = lean_array_push(x_1348, x_1264);
x_1350 = lean_array_push(x_1349, x_1);
x_1351 = lean_array_push(x_1350, x_3);
x_1352 = l_Lean_mkAppN(x_1337, x_1351);
lean_dec(x_1351);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1352);
x_1353 = lean_infer_type(x_1352, x_5, x_6, x_7, x_8, x_1333);
if (lean_obj_tag(x_1353) == 0)
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
x_1354 = lean_ctor_get(x_1353, 0);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1353, 1);
lean_inc(x_1355);
lean_dec(x_1353);
x_1356 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1354, x_6, x_1355);
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
x_1358 = lean_ctor_get(x_1356, 1);
lean_inc(x_1358);
if (lean_is_exclusive(x_1356)) {
 lean_ctor_release(x_1356, 0);
 lean_ctor_release(x_1356, 1);
 x_1359 = x_1356;
} else {
 lean_dec_ref(x_1356);
 x_1359 = lean_box(0);
}
x_1360 = l_Lean_Expr_headBeta(x_1357);
x_1361 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1360, x_1358);
x_1362 = lean_ctor_get(x_1361, 0);
lean_inc(x_1362);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
lean_dec(x_1352);
lean_dec(x_1265);
x_1363 = lean_ctor_get(x_1361, 1);
lean_inc(x_1363);
lean_dec(x_1361);
x_1364 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_1365 = l_Lean_stringToMessageData(x_1364);
lean_dec(x_1364);
x_1366 = l_Lean_indentExpr(x_1360);
if (lean_is_scalar(x_1359)) {
 x_1367 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1367 = x_1359;
 lean_ctor_set_tag(x_1367, 7);
}
lean_ctor_set(x_1367, 0, x_1365);
lean_ctor_set(x_1367, 1, x_1366);
x_1368 = lean_mk_string_unchecked("", 0, 0);
x_1369 = l_Lean_stringToMessageData(x_1368);
lean_dec(x_1368);
x_1370 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1370, 0, x_1367);
lean_ctor_set(x_1370, 1, x_1369);
x_1371 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_1370, x_5, x_6, x_7, x_8, x_1363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1372 = lean_ctor_get(x_1371, 0);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_1371, 1);
lean_inc(x_1373);
if (lean_is_exclusive(x_1371)) {
 lean_ctor_release(x_1371, 0);
 lean_ctor_release(x_1371, 1);
 x_1374 = x_1371;
} else {
 lean_dec_ref(x_1371);
 x_1374 = lean_box(0);
}
if (lean_is_scalar(x_1374)) {
 x_1375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1375 = x_1374;
}
lean_ctor_set(x_1375, 0, x_1372);
lean_ctor_set(x_1375, 1, x_1373);
return x_1375;
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
lean_dec(x_1362);
lean_dec(x_1359);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1376 = lean_ctor_get(x_1361, 1);
lean_inc(x_1376);
if (lean_is_exclusive(x_1361)) {
 lean_ctor_release(x_1361, 0);
 lean_ctor_release(x_1361, 1);
 x_1377 = x_1361;
} else {
 lean_dec_ref(x_1361);
 x_1377 = lean_box(0);
}
if (lean_is_scalar(x_1265)) {
 x_1378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1378 = x_1265;
}
lean_ctor_set(x_1378, 0, x_1352);
lean_ctor_set(x_1378, 1, x_1360);
if (lean_is_scalar(x_1377)) {
 x_1379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1379 = x_1377;
}
lean_ctor_set(x_1379, 0, x_1378);
lean_ctor_set(x_1379, 1, x_1376);
return x_1379;
}
}
else
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
lean_dec(x_1352);
lean_dec(x_1265);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1380 = lean_ctor_get(x_1353, 0);
lean_inc(x_1380);
x_1381 = lean_ctor_get(x_1353, 1);
lean_inc(x_1381);
if (lean_is_exclusive(x_1353)) {
 lean_ctor_release(x_1353, 0);
 lean_ctor_release(x_1353, 1);
 x_1382 = x_1353;
} else {
 lean_dec_ref(x_1353);
 x_1382 = lean_box(0);
}
if (lean_is_scalar(x_1382)) {
 x_1383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1383 = x_1382;
}
lean_ctor_set(x_1383, 0, x_1380);
lean_ctor_set(x_1383, 1, x_1381);
return x_1383;
}
}
else
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_1332);
lean_dec(x_1319);
lean_dec(x_1311);
lean_dec(x_1308);
lean_dec(x_1279);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1262);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_1384 = lean_ctor_get(x_1331, 1);
lean_inc(x_1384);
lean_dec(x_1331);
x_1385 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_1386 = l_Lean_stringToMessageData(x_1385);
lean_dec(x_1385);
x_1387 = l_Lean_indentExpr(x_1329);
x_1388 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1388, 0, x_1386);
lean_ctor_set(x_1388, 1, x_1387);
x_1389 = lean_mk_string_unchecked("", 0, 0);
x_1390 = l_Lean_stringToMessageData(x_1389);
lean_dec(x_1389);
lean_inc(x_1390);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_1390);
lean_ctor_set(x_21, 0, x_1388);
x_1391 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_1391);
lean_ctor_set(x_20, 0, x_21);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_1390);
lean_ctor_set(x_10, 0, x_20);
x_1392 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_1384);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1392;
}
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
lean_dec(x_1329);
lean_dec(x_1319);
lean_dec(x_1311);
lean_dec(x_1308);
lean_dec(x_1279);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1262);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1393 = lean_ctor_get(x_1331, 0);
lean_inc(x_1393);
x_1394 = lean_ctor_get(x_1331, 1);
lean_inc(x_1394);
if (lean_is_exclusive(x_1331)) {
 lean_ctor_release(x_1331, 0);
 lean_ctor_release(x_1331, 1);
 x_1395 = x_1331;
} else {
 lean_dec_ref(x_1331);
 x_1395 = lean_box(0);
}
if (lean_is_scalar(x_1395)) {
 x_1396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1396 = x_1395;
}
lean_ctor_set(x_1396, 0, x_1393);
lean_ctor_set(x_1396, 1, x_1394);
return x_1396;
}
}
else
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
lean_dec(x_1285);
lean_dec(x_1282);
lean_dec(x_1279);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec(x_1270);
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_1261);
lean_dec(x_1258);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1397 = lean_ctor_get(x_1287, 0);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1287, 1);
lean_inc(x_1398);
if (lean_is_exclusive(x_1287)) {
 lean_ctor_release(x_1287, 0);
 lean_ctor_release(x_1287, 1);
 x_1399 = x_1287;
} else {
 lean_dec_ref(x_1287);
 x_1399 = lean_box(0);
}
if (lean_is_scalar(x_1399)) {
 x_1400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1400 = x_1399;
}
lean_ctor_set(x_1400, 0, x_1397);
lean_ctor_set(x_1400, 1, x_1398);
return x_1400;
}
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
lean_dec(x_1282);
lean_dec(x_1279);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec(x_1270);
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_1261);
lean_dec(x_1258);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1401 = lean_ctor_get(x_1284, 0);
lean_inc(x_1401);
x_1402 = lean_ctor_get(x_1284, 1);
lean_inc(x_1402);
if (lean_is_exclusive(x_1284)) {
 lean_ctor_release(x_1284, 0);
 lean_ctor_release(x_1284, 1);
 x_1403 = x_1284;
} else {
 lean_dec_ref(x_1284);
 x_1403 = lean_box(0);
}
if (lean_is_scalar(x_1403)) {
 x_1404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1404 = x_1403;
}
lean_ctor_set(x_1404, 0, x_1401);
lean_ctor_set(x_1404, 1, x_1402);
return x_1404;
}
}
else
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; 
lean_dec(x_1279);
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec(x_1270);
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_1261);
lean_dec(x_1258);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1405 = lean_ctor_get(x_1281, 0);
lean_inc(x_1405);
x_1406 = lean_ctor_get(x_1281, 1);
lean_inc(x_1406);
if (lean_is_exclusive(x_1281)) {
 lean_ctor_release(x_1281, 0);
 lean_ctor_release(x_1281, 1);
 x_1407 = x_1281;
} else {
 lean_dec_ref(x_1281);
 x_1407 = lean_box(0);
}
if (lean_is_scalar(x_1407)) {
 x_1408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1408 = x_1407;
}
lean_ctor_set(x_1408, 0, x_1405);
lean_ctor_set(x_1408, 1, x_1406);
return x_1408;
}
}
else
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
lean_dec(x_1276);
lean_dec(x_1273);
lean_dec(x_1270);
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_1261);
lean_dec(x_1258);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1409 = lean_ctor_get(x_1278, 0);
lean_inc(x_1409);
x_1410 = lean_ctor_get(x_1278, 1);
lean_inc(x_1410);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 lean_ctor_release(x_1278, 1);
 x_1411 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1411 = lean_box(0);
}
if (lean_is_scalar(x_1411)) {
 x_1412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1412 = x_1411;
}
lean_ctor_set(x_1412, 0, x_1409);
lean_ctor_set(x_1412, 1, x_1410);
return x_1412;
}
}
else
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; 
lean_dec(x_1273);
lean_dec(x_1270);
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_1261);
lean_dec(x_1258);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1413 = lean_ctor_get(x_1275, 0);
lean_inc(x_1413);
x_1414 = lean_ctor_get(x_1275, 1);
lean_inc(x_1414);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 x_1415 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1415 = lean_box(0);
}
if (lean_is_scalar(x_1415)) {
 x_1416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1416 = x_1415;
}
lean_ctor_set(x_1416, 0, x_1413);
lean_ctor_set(x_1416, 1, x_1414);
return x_1416;
}
}
else
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
lean_dec(x_1270);
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_1261);
lean_dec(x_1258);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1417 = lean_ctor_get(x_1272, 0);
lean_inc(x_1417);
x_1418 = lean_ctor_get(x_1272, 1);
lean_inc(x_1418);
if (lean_is_exclusive(x_1272)) {
 lean_ctor_release(x_1272, 0);
 lean_ctor_release(x_1272, 1);
 x_1419 = x_1272;
} else {
 lean_dec_ref(x_1272);
 x_1419 = lean_box(0);
}
if (lean_is_scalar(x_1419)) {
 x_1420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1420 = x_1419;
}
lean_ctor_set(x_1420, 0, x_1417);
lean_ctor_set(x_1420, 1, x_1418);
return x_1420;
}
}
else
{
lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_1261);
lean_dec(x_1258);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1421 = lean_ctor_get(x_1269, 0);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_1269, 1);
lean_inc(x_1422);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1423 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1423 = lean_box(0);
}
if (lean_is_scalar(x_1423)) {
 x_1424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1424 = x_1423;
}
lean_ctor_set(x_1424, 0, x_1421);
lean_ctor_set(x_1424, 1, x_1422);
return x_1424;
}
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
lean_dec(x_1265);
lean_dec(x_1264);
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec(x_1261);
lean_dec(x_1258);
lean_free_object(x_21);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1425 = lean_ctor_get(x_1266, 0);
lean_inc(x_1425);
x_1426 = lean_ctor_get(x_1266, 1);
lean_inc(x_1426);
if (lean_is_exclusive(x_1266)) {
 lean_ctor_release(x_1266, 0);
 lean_ctor_release(x_1266, 1);
 x_1427 = x_1266;
} else {
 lean_dec_ref(x_1266);
 x_1427 = lean_box(0);
}
if (lean_is_scalar(x_1427)) {
 x_1428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1428 = x_1427;
}
lean_ctor_set(x_1428, 0, x_1425);
lean_ctor_set(x_1428, 1, x_1426);
return x_1428;
}
}
}
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
x_1429 = lean_ctor_get(x_21, 0);
x_1430 = lean_ctor_get(x_21, 1);
lean_inc(x_1430);
lean_inc(x_1429);
lean_dec(x_21);
x_1431 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_4, x_6, x_23);
x_1432 = lean_ctor_get(x_1431, 0);
lean_inc(x_1432);
x_1433 = lean_ctor_get(x_1431, 1);
lean_inc(x_1433);
if (lean_is_exclusive(x_1431)) {
 lean_ctor_release(x_1431, 0);
 lean_ctor_release(x_1431, 1);
 x_1434 = x_1431;
} else {
 lean_dec_ref(x_1431);
 x_1434 = lean_box(0);
}
x_1435 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1432, x_1433);
lean_dec(x_1432);
x_1436 = lean_ctor_get(x_1435, 0);
lean_inc(x_1436);
if (lean_obj_tag(x_1436) == 0)
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_1437 = lean_ctor_get(x_1435, 1);
lean_inc(x_1437);
lean_dec(x_1435);
x_1438 = lean_mk_string_unchecked("Lean.Elab.Calc", 14, 14);
x_1439 = lean_mk_string_unchecked("Lean.Elab.Term.mkCalcTrans", 26, 26);
x_1440 = lean_unsigned_to_nat(31u);
x_1441 = lean_unsigned_to_nat(72u);
x_1442 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_1443 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1438, x_1439, x_1440, x_1441, x_1442);
lean_dec(x_1442);
lean_dec(x_1439);
lean_dec(x_1438);
x_1444 = l_panic___at___Lean_Elab_Term_mkCalcTrans_spec__0(x_1443, x_5, x_6, x_7, x_8, x_1437);
return x_1444;
}
else
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
x_1445 = lean_ctor_get(x_1436, 0);
lean_inc(x_1445);
if (lean_is_exclusive(x_1436)) {
 lean_ctor_release(x_1436, 0);
 x_1446 = x_1436;
} else {
 lean_dec_ref(x_1436);
 x_1446 = lean_box(0);
}
x_1447 = lean_ctor_get(x_1445, 1);
lean_inc(x_1447);
x_1448 = lean_ctor_get(x_1435, 1);
lean_inc(x_1448);
if (lean_is_exclusive(x_1435)) {
 lean_ctor_release(x_1435, 0);
 lean_ctor_release(x_1435, 1);
 x_1449 = x_1435;
} else {
 lean_dec_ref(x_1435);
 x_1449 = lean_box(0);
}
x_1450 = lean_ctor_get(x_1445, 0);
lean_inc(x_1450);
if (lean_is_exclusive(x_1445)) {
 lean_ctor_release(x_1445, 0);
 lean_ctor_release(x_1445, 1);
 x_1451 = x_1445;
} else {
 lean_dec_ref(x_1445);
 x_1451 = lean_box(0);
}
x_1452 = lean_ctor_get(x_1447, 1);
lean_inc(x_1452);
if (lean_is_exclusive(x_1447)) {
 lean_ctor_release(x_1447, 0);
 lean_ctor_release(x_1447, 1);
 x_1453 = x_1447;
} else {
 lean_dec_ref(x_1447);
 x_1453 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_1454 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_26, x_5, x_6, x_7, x_8, x_1448);
if (lean_obj_tag(x_1454) == 0)
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1455 = lean_ctor_get(x_1454, 0);
lean_inc(x_1455);
x_1456 = lean_ctor_get(x_1454, 1);
lean_inc(x_1456);
lean_dec(x_1454);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1450);
x_1457 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1450, x_5, x_6, x_7, x_8, x_1456);
if (lean_obj_tag(x_1457) == 0)
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1457, 1);
lean_inc(x_1459);
lean_dec(x_1457);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1429);
x_1460 = lean_infer_type(x_1429, x_5, x_6, x_7, x_8, x_1459);
if (lean_obj_tag(x_1460) == 0)
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
x_1461 = lean_ctor_get(x_1460, 0);
lean_inc(x_1461);
x_1462 = lean_ctor_get(x_1460, 1);
lean_inc(x_1462);
lean_dec(x_1460);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1430);
x_1463 = lean_infer_type(x_1430, x_5, x_6, x_7, x_8, x_1462);
if (lean_obj_tag(x_1463) == 0)
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
x_1465 = lean_ctor_get(x_1463, 1);
lean_inc(x_1465);
lean_dec(x_1463);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1452);
x_1466 = lean_infer_type(x_1452, x_5, x_6, x_7, x_8, x_1465);
if (lean_obj_tag(x_1466) == 0)
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; 
x_1467 = lean_ctor_get(x_1466, 0);
lean_inc(x_1467);
x_1468 = lean_ctor_get(x_1466, 1);
lean_inc(x_1468);
lean_dec(x_1466);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1461);
x_1469 = l_Lean_Meta_getLevel(x_1461, x_5, x_6, x_7, x_8, x_1468);
if (lean_obj_tag(x_1469) == 0)
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
x_1470 = lean_ctor_get(x_1469, 0);
lean_inc(x_1470);
x_1471 = lean_ctor_get(x_1469, 1);
lean_inc(x_1471);
lean_dec(x_1469);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1464);
x_1472 = l_Lean_Meta_getLevel(x_1464, x_5, x_6, x_7, x_8, x_1471);
if (lean_obj_tag(x_1472) == 0)
{
lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
x_1473 = lean_ctor_get(x_1472, 0);
lean_inc(x_1473);
x_1474 = lean_ctor_get(x_1472, 1);
lean_inc(x_1474);
lean_dec(x_1472);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1467);
x_1475 = l_Lean_Meta_getLevel(x_1467, x_5, x_6, x_7, x_8, x_1474);
if (lean_obj_tag(x_1475) == 0)
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; uint8_t x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
x_1476 = lean_ctor_get(x_1475, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1475, 1);
lean_inc(x_1477);
lean_dec(x_1475);
x_1478 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1477);
x_1479 = lean_ctor_get(x_1478, 0);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1478, 1);
lean_inc(x_1480);
if (lean_is_exclusive(x_1478)) {
 lean_ctor_release(x_1478, 0);
 lean_ctor_release(x_1478, 1);
 x_1481 = x_1478;
} else {
 lean_dec_ref(x_1478);
 x_1481 = lean_box(0);
}
lean_inc(x_1479);
x_1482 = l_Lean_Expr_sort___override(x_1479);
lean_inc(x_1467);
x_1483 = l_Lean_mkArrow(x_1467, x_1482, x_7, x_8, x_1480);
x_1484 = lean_ctor_get(x_1483, 0);
lean_inc(x_1484);
x_1485 = lean_ctor_get(x_1483, 1);
lean_inc(x_1485);
if (lean_is_exclusive(x_1483)) {
 lean_ctor_release(x_1483, 0);
 lean_ctor_release(x_1483, 1);
 x_1486 = x_1483;
} else {
 lean_dec_ref(x_1483);
 x_1486 = lean_box(0);
}
lean_inc(x_1461);
x_1487 = l_Lean_mkArrow(x_1461, x_1484, x_7, x_8, x_1485);
x_1488 = lean_ctor_get(x_1487, 0);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1487, 1);
lean_inc(x_1489);
if (lean_is_exclusive(x_1487)) {
 lean_ctor_release(x_1487, 0);
 lean_ctor_release(x_1487, 1);
 x_1490 = x_1487;
} else {
 lean_dec_ref(x_1487);
 x_1490 = lean_box(0);
}
if (lean_is_scalar(x_1446)) {
 x_1491 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1491 = x_1446;
}
lean_ctor_set(x_1491, 0, x_1488);
x_1492 = lean_box(0);
x_1493 = lean_box(0);
x_1494 = lean_unbox(x_1492);
lean_inc(x_5);
x_1495 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1491, x_1494, x_1493, x_5, x_6, x_7, x_8, x_1489);
x_1496 = lean_ctor_get(x_1495, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1495, 1);
lean_inc(x_1497);
if (lean_is_exclusive(x_1495)) {
 lean_ctor_release(x_1495, 0);
 lean_ctor_release(x_1495, 1);
 x_1498 = x_1495;
} else {
 lean_dec_ref(x_1495);
 x_1498 = lean_box(0);
}
x_1499 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_1499);
x_1500 = l_Lean_Name_mkStr1(x_1499);
x_1501 = lean_box(0);
if (lean_is_scalar(x_1498)) {
 x_1502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1502 = x_1498;
 lean_ctor_set_tag(x_1502, 1);
}
lean_ctor_set(x_1502, 0, x_1476);
lean_ctor_set(x_1502, 1, x_1501);
if (lean_is_scalar(x_1490)) {
 x_1503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1503 = x_1490;
 lean_ctor_set_tag(x_1503, 1);
}
lean_ctor_set(x_1503, 0, x_1473);
lean_ctor_set(x_1503, 1, x_1502);
if (lean_is_scalar(x_1486)) {
 x_1504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1504 = x_1486;
 lean_ctor_set_tag(x_1504, 1);
}
lean_ctor_set(x_1504, 0, x_1470);
lean_ctor_set(x_1504, 1, x_1503);
if (lean_is_scalar(x_1481)) {
 x_1505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1505 = x_1481;
 lean_ctor_set_tag(x_1505, 1);
}
lean_ctor_set(x_1505, 0, x_1479);
lean_ctor_set(x_1505, 1, x_1504);
if (lean_is_scalar(x_1451)) {
 x_1506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1506 = x_1451;
 lean_ctor_set_tag(x_1506, 1);
}
lean_ctor_set(x_1506, 0, x_1458);
lean_ctor_set(x_1506, 1, x_1505);
if (lean_is_scalar(x_1449)) {
 x_1507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1507 = x_1449;
 lean_ctor_set_tag(x_1507, 1);
}
lean_ctor_set(x_1507, 0, x_1455);
lean_ctor_set(x_1507, 1, x_1506);
lean_inc(x_1507);
x_1508 = l_Lean_Expr_const___override(x_1500, x_1507);
x_1509 = lean_unsigned_to_nat(6u);
x_1510 = lean_mk_empty_array_with_capacity(x_1509);
lean_inc(x_1461);
x_1511 = lean_array_push(x_1510, x_1461);
lean_inc(x_1464);
x_1512 = lean_array_push(x_1511, x_1464);
lean_inc(x_1467);
x_1513 = lean_array_push(x_1512, x_1467);
lean_inc(x_26);
x_1514 = lean_array_push(x_1513, x_26);
lean_inc(x_1450);
x_1515 = lean_array_push(x_1514, x_1450);
lean_inc(x_1496);
x_1516 = lean_array_push(x_1515, x_1496);
x_1517 = l_Lean_mkAppN(x_1508, x_1516);
lean_dec(x_1516);
x_1518 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1517);
x_1519 = l_Lean_Meta_trySynthInstance(x_1517, x_1518, x_5, x_6, x_7, x_8, x_1497);
if (lean_obj_tag(x_1519) == 0)
{
lean_object* x_1520; 
x_1520 = lean_ctor_get(x_1519, 0);
lean_inc(x_1520);
if (lean_obj_tag(x_1520) == 1)
{
lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; 
lean_dec(x_1517);
lean_free_object(x_20);
lean_free_object(x_10);
x_1521 = lean_ctor_get(x_1519, 1);
lean_inc(x_1521);
lean_dec(x_1519);
x_1522 = lean_ctor_get(x_1520, 0);
lean_inc(x_1522);
lean_dec(x_1520);
x_1523 = lean_mk_string_unchecked("trans", 5, 5);
x_1524 = l_Lean_Name_mkStr2(x_1499, x_1523);
x_1525 = l_Lean_Expr_const___override(x_1524, x_1507);
x_1526 = lean_unsigned_to_nat(12u);
x_1527 = lean_mk_empty_array_with_capacity(x_1526);
x_1528 = lean_array_push(x_1527, x_1461);
x_1529 = lean_array_push(x_1528, x_1464);
x_1530 = lean_array_push(x_1529, x_1467);
x_1531 = lean_array_push(x_1530, x_26);
x_1532 = lean_array_push(x_1531, x_1450);
x_1533 = lean_array_push(x_1532, x_1496);
x_1534 = lean_array_push(x_1533, x_1522);
x_1535 = lean_array_push(x_1534, x_1429);
x_1536 = lean_array_push(x_1535, x_1430);
x_1537 = lean_array_push(x_1536, x_1452);
x_1538 = lean_array_push(x_1537, x_1);
x_1539 = lean_array_push(x_1538, x_3);
x_1540 = l_Lean_mkAppN(x_1525, x_1539);
lean_dec(x_1539);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1540);
x_1541 = lean_infer_type(x_1540, x_5, x_6, x_7, x_8, x_1521);
if (lean_obj_tag(x_1541) == 0)
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
x_1542 = lean_ctor_get(x_1541, 0);
lean_inc(x_1542);
x_1543 = lean_ctor_get(x_1541, 1);
lean_inc(x_1543);
lean_dec(x_1541);
x_1544 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1542, x_6, x_1543);
x_1545 = lean_ctor_get(x_1544, 0);
lean_inc(x_1545);
x_1546 = lean_ctor_get(x_1544, 1);
lean_inc(x_1546);
if (lean_is_exclusive(x_1544)) {
 lean_ctor_release(x_1544, 0);
 lean_ctor_release(x_1544, 1);
 x_1547 = x_1544;
} else {
 lean_dec_ref(x_1544);
 x_1547 = lean_box(0);
}
x_1548 = l_Lean_Expr_headBeta(x_1545);
x_1549 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1548, x_1546);
x_1550 = lean_ctor_get(x_1549, 0);
lean_inc(x_1550);
if (lean_obj_tag(x_1550) == 0)
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
lean_dec(x_1540);
lean_dec(x_1453);
x_1551 = lean_ctor_get(x_1549, 1);
lean_inc(x_1551);
lean_dec(x_1549);
x_1552 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_1553 = l_Lean_stringToMessageData(x_1552);
lean_dec(x_1552);
x_1554 = l_Lean_indentExpr(x_1548);
if (lean_is_scalar(x_1547)) {
 x_1555 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1555 = x_1547;
 lean_ctor_set_tag(x_1555, 7);
}
lean_ctor_set(x_1555, 0, x_1553);
lean_ctor_set(x_1555, 1, x_1554);
x_1556 = lean_mk_string_unchecked("", 0, 0);
x_1557 = l_Lean_stringToMessageData(x_1556);
lean_dec(x_1556);
if (lean_is_scalar(x_1434)) {
 x_1558 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1558 = x_1434;
 lean_ctor_set_tag(x_1558, 7);
}
lean_ctor_set(x_1558, 0, x_1555);
lean_ctor_set(x_1558, 1, x_1557);
x_1559 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_1558, x_5, x_6, x_7, x_8, x_1551);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1560 = lean_ctor_get(x_1559, 0);
lean_inc(x_1560);
x_1561 = lean_ctor_get(x_1559, 1);
lean_inc(x_1561);
if (lean_is_exclusive(x_1559)) {
 lean_ctor_release(x_1559, 0);
 lean_ctor_release(x_1559, 1);
 x_1562 = x_1559;
} else {
 lean_dec_ref(x_1559);
 x_1562 = lean_box(0);
}
if (lean_is_scalar(x_1562)) {
 x_1563 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1563 = x_1562;
}
lean_ctor_set(x_1563, 0, x_1560);
lean_ctor_set(x_1563, 1, x_1561);
return x_1563;
}
else
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; 
lean_dec(x_1550);
lean_dec(x_1547);
lean_dec(x_1434);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1564 = lean_ctor_get(x_1549, 1);
lean_inc(x_1564);
if (lean_is_exclusive(x_1549)) {
 lean_ctor_release(x_1549, 0);
 lean_ctor_release(x_1549, 1);
 x_1565 = x_1549;
} else {
 lean_dec_ref(x_1549);
 x_1565 = lean_box(0);
}
if (lean_is_scalar(x_1453)) {
 x_1566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1566 = x_1453;
}
lean_ctor_set(x_1566, 0, x_1540);
lean_ctor_set(x_1566, 1, x_1548);
if (lean_is_scalar(x_1565)) {
 x_1567 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1567 = x_1565;
}
lean_ctor_set(x_1567, 0, x_1566);
lean_ctor_set(x_1567, 1, x_1564);
return x_1567;
}
}
else
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; 
lean_dec(x_1540);
lean_dec(x_1453);
lean_dec(x_1434);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1568 = lean_ctor_get(x_1541, 0);
lean_inc(x_1568);
x_1569 = lean_ctor_get(x_1541, 1);
lean_inc(x_1569);
if (lean_is_exclusive(x_1541)) {
 lean_ctor_release(x_1541, 0);
 lean_ctor_release(x_1541, 1);
 x_1570 = x_1541;
} else {
 lean_dec_ref(x_1541);
 x_1570 = lean_box(0);
}
if (lean_is_scalar(x_1570)) {
 x_1571 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1571 = x_1570;
}
lean_ctor_set(x_1571, 0, x_1568);
lean_ctor_set(x_1571, 1, x_1569);
return x_1571;
}
}
else
{
lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
lean_dec(x_1520);
lean_dec(x_1507);
lean_dec(x_1499);
lean_dec(x_1496);
lean_dec(x_1467);
lean_dec(x_1464);
lean_dec(x_1461);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1430);
lean_dec(x_1429);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_1);
x_1572 = lean_ctor_get(x_1519, 1);
lean_inc(x_1572);
lean_dec(x_1519);
x_1573 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_1574 = l_Lean_stringToMessageData(x_1573);
lean_dec(x_1573);
x_1575 = l_Lean_indentExpr(x_1517);
if (lean_is_scalar(x_1434)) {
 x_1576 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1576 = x_1434;
 lean_ctor_set_tag(x_1576, 7);
}
lean_ctor_set(x_1576, 0, x_1574);
lean_ctor_set(x_1576, 1, x_1575);
x_1577 = lean_mk_string_unchecked("", 0, 0);
x_1578 = l_Lean_stringToMessageData(x_1577);
lean_dec(x_1577);
lean_inc(x_1578);
x_1579 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1579, 0, x_1576);
lean_ctor_set(x_1579, 1, x_1578);
x_1580 = l_Lean_useDiagnosticMsg;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_1580);
lean_ctor_set(x_20, 0, x_1579);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_1578);
lean_ctor_set(x_10, 0, x_20);
x_1581 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_1572);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1581;
}
}
else
{
lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; 
lean_dec(x_1517);
lean_dec(x_1507);
lean_dec(x_1499);
lean_dec(x_1496);
lean_dec(x_1467);
lean_dec(x_1464);
lean_dec(x_1461);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1582 = lean_ctor_get(x_1519, 0);
lean_inc(x_1582);
x_1583 = lean_ctor_get(x_1519, 1);
lean_inc(x_1583);
if (lean_is_exclusive(x_1519)) {
 lean_ctor_release(x_1519, 0);
 lean_ctor_release(x_1519, 1);
 x_1584 = x_1519;
} else {
 lean_dec_ref(x_1519);
 x_1584 = lean_box(0);
}
if (lean_is_scalar(x_1584)) {
 x_1585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1585 = x_1584;
}
lean_ctor_set(x_1585, 0, x_1582);
lean_ctor_set(x_1585, 1, x_1583);
return x_1585;
}
}
else
{
lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; 
lean_dec(x_1473);
lean_dec(x_1470);
lean_dec(x_1467);
lean_dec(x_1464);
lean_dec(x_1461);
lean_dec(x_1458);
lean_dec(x_1455);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1451);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1446);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1586 = lean_ctor_get(x_1475, 0);
lean_inc(x_1586);
x_1587 = lean_ctor_get(x_1475, 1);
lean_inc(x_1587);
if (lean_is_exclusive(x_1475)) {
 lean_ctor_release(x_1475, 0);
 lean_ctor_release(x_1475, 1);
 x_1588 = x_1475;
} else {
 lean_dec_ref(x_1475);
 x_1588 = lean_box(0);
}
if (lean_is_scalar(x_1588)) {
 x_1589 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1589 = x_1588;
}
lean_ctor_set(x_1589, 0, x_1586);
lean_ctor_set(x_1589, 1, x_1587);
return x_1589;
}
}
else
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; 
lean_dec(x_1470);
lean_dec(x_1467);
lean_dec(x_1464);
lean_dec(x_1461);
lean_dec(x_1458);
lean_dec(x_1455);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1451);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1446);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1590 = lean_ctor_get(x_1472, 0);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1472, 1);
lean_inc(x_1591);
if (lean_is_exclusive(x_1472)) {
 lean_ctor_release(x_1472, 0);
 lean_ctor_release(x_1472, 1);
 x_1592 = x_1472;
} else {
 lean_dec_ref(x_1472);
 x_1592 = lean_box(0);
}
if (lean_is_scalar(x_1592)) {
 x_1593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1593 = x_1592;
}
lean_ctor_set(x_1593, 0, x_1590);
lean_ctor_set(x_1593, 1, x_1591);
return x_1593;
}
}
else
{
lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; 
lean_dec(x_1467);
lean_dec(x_1464);
lean_dec(x_1461);
lean_dec(x_1458);
lean_dec(x_1455);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1451);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1446);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1594 = lean_ctor_get(x_1469, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1469, 1);
lean_inc(x_1595);
if (lean_is_exclusive(x_1469)) {
 lean_ctor_release(x_1469, 0);
 lean_ctor_release(x_1469, 1);
 x_1596 = x_1469;
} else {
 lean_dec_ref(x_1469);
 x_1596 = lean_box(0);
}
if (lean_is_scalar(x_1596)) {
 x_1597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1597 = x_1596;
}
lean_ctor_set(x_1597, 0, x_1594);
lean_ctor_set(x_1597, 1, x_1595);
return x_1597;
}
}
else
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; 
lean_dec(x_1464);
lean_dec(x_1461);
lean_dec(x_1458);
lean_dec(x_1455);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1451);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1446);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1598 = lean_ctor_get(x_1466, 0);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_1466, 1);
lean_inc(x_1599);
if (lean_is_exclusive(x_1466)) {
 lean_ctor_release(x_1466, 0);
 lean_ctor_release(x_1466, 1);
 x_1600 = x_1466;
} else {
 lean_dec_ref(x_1466);
 x_1600 = lean_box(0);
}
if (lean_is_scalar(x_1600)) {
 x_1601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1601 = x_1600;
}
lean_ctor_set(x_1601, 0, x_1598);
lean_ctor_set(x_1601, 1, x_1599);
return x_1601;
}
}
else
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; 
lean_dec(x_1461);
lean_dec(x_1458);
lean_dec(x_1455);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1451);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1446);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1602 = lean_ctor_get(x_1463, 0);
lean_inc(x_1602);
x_1603 = lean_ctor_get(x_1463, 1);
lean_inc(x_1603);
if (lean_is_exclusive(x_1463)) {
 lean_ctor_release(x_1463, 0);
 lean_ctor_release(x_1463, 1);
 x_1604 = x_1463;
} else {
 lean_dec_ref(x_1463);
 x_1604 = lean_box(0);
}
if (lean_is_scalar(x_1604)) {
 x_1605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1605 = x_1604;
}
lean_ctor_set(x_1605, 0, x_1602);
lean_ctor_set(x_1605, 1, x_1603);
return x_1605;
}
}
else
{
lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; 
lean_dec(x_1458);
lean_dec(x_1455);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1451);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1446);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1606 = lean_ctor_get(x_1460, 0);
lean_inc(x_1606);
x_1607 = lean_ctor_get(x_1460, 1);
lean_inc(x_1607);
if (lean_is_exclusive(x_1460)) {
 lean_ctor_release(x_1460, 0);
 lean_ctor_release(x_1460, 1);
 x_1608 = x_1460;
} else {
 lean_dec_ref(x_1460);
 x_1608 = lean_box(0);
}
if (lean_is_scalar(x_1608)) {
 x_1609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1609 = x_1608;
}
lean_ctor_set(x_1609, 0, x_1606);
lean_ctor_set(x_1609, 1, x_1607);
return x_1609;
}
}
else
{
lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; 
lean_dec(x_1455);
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1451);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1446);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1610 = lean_ctor_get(x_1457, 0);
lean_inc(x_1610);
x_1611 = lean_ctor_get(x_1457, 1);
lean_inc(x_1611);
if (lean_is_exclusive(x_1457)) {
 lean_ctor_release(x_1457, 0);
 lean_ctor_release(x_1457, 1);
 x_1612 = x_1457;
} else {
 lean_dec_ref(x_1457);
 x_1612 = lean_box(0);
}
if (lean_is_scalar(x_1612)) {
 x_1613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1613 = x_1612;
}
lean_ctor_set(x_1613, 0, x_1610);
lean_ctor_set(x_1613, 1, x_1611);
return x_1613;
}
}
else
{
lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
lean_dec(x_1453);
lean_dec(x_1452);
lean_dec(x_1451);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1446);
lean_dec(x_1434);
lean_dec(x_1430);
lean_dec(x_1429);
lean_free_object(x_20);
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1614 = lean_ctor_get(x_1454, 0);
lean_inc(x_1614);
x_1615 = lean_ctor_get(x_1454, 1);
lean_inc(x_1615);
if (lean_is_exclusive(x_1454)) {
 lean_ctor_release(x_1454, 0);
 lean_ctor_release(x_1454, 1);
 x_1616 = x_1454;
} else {
 lean_dec_ref(x_1454);
 x_1616 = lean_box(0);
}
if (lean_is_scalar(x_1616)) {
 x_1617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1617 = x_1616;
}
lean_ctor_set(x_1617, 0, x_1614);
lean_ctor_set(x_1617, 1, x_1615);
return x_1617;
}
}
}
}
else
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; 
x_1618 = lean_ctor_get(x_20, 0);
lean_inc(x_1618);
lean_dec(x_20);
x_1619 = lean_ctor_get(x_21, 0);
lean_inc(x_1619);
x_1620 = lean_ctor_get(x_21, 1);
lean_inc(x_1620);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_1621 = x_21;
} else {
 lean_dec_ref(x_21);
 x_1621 = lean_box(0);
}
x_1622 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_4, x_6, x_23);
x_1623 = lean_ctor_get(x_1622, 0);
lean_inc(x_1623);
x_1624 = lean_ctor_get(x_1622, 1);
lean_inc(x_1624);
if (lean_is_exclusive(x_1622)) {
 lean_ctor_release(x_1622, 0);
 lean_ctor_release(x_1622, 1);
 x_1625 = x_1622;
} else {
 lean_dec_ref(x_1622);
 x_1625 = lean_box(0);
}
x_1626 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1623, x_1624);
lean_dec(x_1623);
x_1627 = lean_ctor_get(x_1626, 0);
lean_inc(x_1627);
if (lean_obj_tag(x_1627) == 0)
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_1628 = lean_ctor_get(x_1626, 1);
lean_inc(x_1628);
lean_dec(x_1626);
x_1629 = lean_mk_string_unchecked("Lean.Elab.Calc", 14, 14);
x_1630 = lean_mk_string_unchecked("Lean.Elab.Term.mkCalcTrans", 26, 26);
x_1631 = lean_unsigned_to_nat(31u);
x_1632 = lean_unsigned_to_nat(72u);
x_1633 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_1634 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1629, x_1630, x_1631, x_1632, x_1633);
lean_dec(x_1633);
lean_dec(x_1630);
lean_dec(x_1629);
x_1635 = l_panic___at___Lean_Elab_Term_mkCalcTrans_spec__0(x_1634, x_5, x_6, x_7, x_8, x_1628);
return x_1635;
}
else
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
x_1636 = lean_ctor_get(x_1627, 0);
lean_inc(x_1636);
if (lean_is_exclusive(x_1627)) {
 lean_ctor_release(x_1627, 0);
 x_1637 = x_1627;
} else {
 lean_dec_ref(x_1627);
 x_1637 = lean_box(0);
}
x_1638 = lean_ctor_get(x_1636, 1);
lean_inc(x_1638);
x_1639 = lean_ctor_get(x_1626, 1);
lean_inc(x_1639);
if (lean_is_exclusive(x_1626)) {
 lean_ctor_release(x_1626, 0);
 lean_ctor_release(x_1626, 1);
 x_1640 = x_1626;
} else {
 lean_dec_ref(x_1626);
 x_1640 = lean_box(0);
}
x_1641 = lean_ctor_get(x_1636, 0);
lean_inc(x_1641);
if (lean_is_exclusive(x_1636)) {
 lean_ctor_release(x_1636, 0);
 lean_ctor_release(x_1636, 1);
 x_1642 = x_1636;
} else {
 lean_dec_ref(x_1636);
 x_1642 = lean_box(0);
}
x_1643 = lean_ctor_get(x_1638, 1);
lean_inc(x_1643);
if (lean_is_exclusive(x_1638)) {
 lean_ctor_release(x_1638, 0);
 lean_ctor_release(x_1638, 1);
 x_1644 = x_1638;
} else {
 lean_dec_ref(x_1638);
 x_1644 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1618);
x_1645 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1618, x_5, x_6, x_7, x_8, x_1639);
if (lean_obj_tag(x_1645) == 0)
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; 
x_1646 = lean_ctor_get(x_1645, 0);
lean_inc(x_1646);
x_1647 = lean_ctor_get(x_1645, 1);
lean_inc(x_1647);
lean_dec(x_1645);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1641);
x_1648 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1641, x_5, x_6, x_7, x_8, x_1647);
if (lean_obj_tag(x_1648) == 0)
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; 
x_1649 = lean_ctor_get(x_1648, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1648, 1);
lean_inc(x_1650);
lean_dec(x_1648);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1619);
x_1651 = lean_infer_type(x_1619, x_5, x_6, x_7, x_8, x_1650);
if (lean_obj_tag(x_1651) == 0)
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
x_1652 = lean_ctor_get(x_1651, 0);
lean_inc(x_1652);
x_1653 = lean_ctor_get(x_1651, 1);
lean_inc(x_1653);
lean_dec(x_1651);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1620);
x_1654 = lean_infer_type(x_1620, x_5, x_6, x_7, x_8, x_1653);
if (lean_obj_tag(x_1654) == 0)
{
lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
x_1655 = lean_ctor_get(x_1654, 0);
lean_inc(x_1655);
x_1656 = lean_ctor_get(x_1654, 1);
lean_inc(x_1656);
lean_dec(x_1654);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1643);
x_1657 = lean_infer_type(x_1643, x_5, x_6, x_7, x_8, x_1656);
if (lean_obj_tag(x_1657) == 0)
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; 
x_1658 = lean_ctor_get(x_1657, 0);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1657, 1);
lean_inc(x_1659);
lean_dec(x_1657);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1652);
x_1660 = l_Lean_Meta_getLevel(x_1652, x_5, x_6, x_7, x_8, x_1659);
if (lean_obj_tag(x_1660) == 0)
{
lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; 
x_1661 = lean_ctor_get(x_1660, 0);
lean_inc(x_1661);
x_1662 = lean_ctor_get(x_1660, 1);
lean_inc(x_1662);
lean_dec(x_1660);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1655);
x_1663 = l_Lean_Meta_getLevel(x_1655, x_5, x_6, x_7, x_8, x_1662);
if (lean_obj_tag(x_1663) == 0)
{
lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
x_1664 = lean_ctor_get(x_1663, 0);
lean_inc(x_1664);
x_1665 = lean_ctor_get(x_1663, 1);
lean_inc(x_1665);
lean_dec(x_1663);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1658);
x_1666 = l_Lean_Meta_getLevel(x_1658, x_5, x_6, x_7, x_8, x_1665);
if (lean_obj_tag(x_1666) == 0)
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; uint8_t x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; 
x_1667 = lean_ctor_get(x_1666, 0);
lean_inc(x_1667);
x_1668 = lean_ctor_get(x_1666, 1);
lean_inc(x_1668);
lean_dec(x_1666);
x_1669 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1668);
x_1670 = lean_ctor_get(x_1669, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1669, 1);
lean_inc(x_1671);
if (lean_is_exclusive(x_1669)) {
 lean_ctor_release(x_1669, 0);
 lean_ctor_release(x_1669, 1);
 x_1672 = x_1669;
} else {
 lean_dec_ref(x_1669);
 x_1672 = lean_box(0);
}
lean_inc(x_1670);
x_1673 = l_Lean_Expr_sort___override(x_1670);
lean_inc(x_1658);
x_1674 = l_Lean_mkArrow(x_1658, x_1673, x_7, x_8, x_1671);
x_1675 = lean_ctor_get(x_1674, 0);
lean_inc(x_1675);
x_1676 = lean_ctor_get(x_1674, 1);
lean_inc(x_1676);
if (lean_is_exclusive(x_1674)) {
 lean_ctor_release(x_1674, 0);
 lean_ctor_release(x_1674, 1);
 x_1677 = x_1674;
} else {
 lean_dec_ref(x_1674);
 x_1677 = lean_box(0);
}
lean_inc(x_1652);
x_1678 = l_Lean_mkArrow(x_1652, x_1675, x_7, x_8, x_1676);
x_1679 = lean_ctor_get(x_1678, 0);
lean_inc(x_1679);
x_1680 = lean_ctor_get(x_1678, 1);
lean_inc(x_1680);
if (lean_is_exclusive(x_1678)) {
 lean_ctor_release(x_1678, 0);
 lean_ctor_release(x_1678, 1);
 x_1681 = x_1678;
} else {
 lean_dec_ref(x_1678);
 x_1681 = lean_box(0);
}
if (lean_is_scalar(x_1637)) {
 x_1682 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1682 = x_1637;
}
lean_ctor_set(x_1682, 0, x_1679);
x_1683 = lean_box(0);
x_1684 = lean_box(0);
x_1685 = lean_unbox(x_1683);
lean_inc(x_5);
x_1686 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1682, x_1685, x_1684, x_5, x_6, x_7, x_8, x_1680);
x_1687 = lean_ctor_get(x_1686, 0);
lean_inc(x_1687);
x_1688 = lean_ctor_get(x_1686, 1);
lean_inc(x_1688);
if (lean_is_exclusive(x_1686)) {
 lean_ctor_release(x_1686, 0);
 lean_ctor_release(x_1686, 1);
 x_1689 = x_1686;
} else {
 lean_dec_ref(x_1686);
 x_1689 = lean_box(0);
}
x_1690 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_1690);
x_1691 = l_Lean_Name_mkStr1(x_1690);
x_1692 = lean_box(0);
if (lean_is_scalar(x_1689)) {
 x_1693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1693 = x_1689;
 lean_ctor_set_tag(x_1693, 1);
}
lean_ctor_set(x_1693, 0, x_1667);
lean_ctor_set(x_1693, 1, x_1692);
if (lean_is_scalar(x_1681)) {
 x_1694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1694 = x_1681;
 lean_ctor_set_tag(x_1694, 1);
}
lean_ctor_set(x_1694, 0, x_1664);
lean_ctor_set(x_1694, 1, x_1693);
if (lean_is_scalar(x_1677)) {
 x_1695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1695 = x_1677;
 lean_ctor_set_tag(x_1695, 1);
}
lean_ctor_set(x_1695, 0, x_1661);
lean_ctor_set(x_1695, 1, x_1694);
if (lean_is_scalar(x_1672)) {
 x_1696 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1696 = x_1672;
 lean_ctor_set_tag(x_1696, 1);
}
lean_ctor_set(x_1696, 0, x_1670);
lean_ctor_set(x_1696, 1, x_1695);
if (lean_is_scalar(x_1642)) {
 x_1697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1697 = x_1642;
 lean_ctor_set_tag(x_1697, 1);
}
lean_ctor_set(x_1697, 0, x_1649);
lean_ctor_set(x_1697, 1, x_1696);
if (lean_is_scalar(x_1640)) {
 x_1698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1698 = x_1640;
 lean_ctor_set_tag(x_1698, 1);
}
lean_ctor_set(x_1698, 0, x_1646);
lean_ctor_set(x_1698, 1, x_1697);
lean_inc(x_1698);
x_1699 = l_Lean_Expr_const___override(x_1691, x_1698);
x_1700 = lean_unsigned_to_nat(6u);
x_1701 = lean_mk_empty_array_with_capacity(x_1700);
lean_inc(x_1652);
x_1702 = lean_array_push(x_1701, x_1652);
lean_inc(x_1655);
x_1703 = lean_array_push(x_1702, x_1655);
lean_inc(x_1658);
x_1704 = lean_array_push(x_1703, x_1658);
lean_inc(x_1618);
x_1705 = lean_array_push(x_1704, x_1618);
lean_inc(x_1641);
x_1706 = lean_array_push(x_1705, x_1641);
lean_inc(x_1687);
x_1707 = lean_array_push(x_1706, x_1687);
x_1708 = l_Lean_mkAppN(x_1699, x_1707);
lean_dec(x_1707);
x_1709 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1708);
x_1710 = l_Lean_Meta_trySynthInstance(x_1708, x_1709, x_5, x_6, x_7, x_8, x_1688);
if (lean_obj_tag(x_1710) == 0)
{
lean_object* x_1711; 
x_1711 = lean_ctor_get(x_1710, 0);
lean_inc(x_1711);
if (lean_obj_tag(x_1711) == 1)
{
lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; 
lean_dec(x_1708);
lean_dec(x_1621);
lean_free_object(x_10);
x_1712 = lean_ctor_get(x_1710, 1);
lean_inc(x_1712);
lean_dec(x_1710);
x_1713 = lean_ctor_get(x_1711, 0);
lean_inc(x_1713);
lean_dec(x_1711);
x_1714 = lean_mk_string_unchecked("trans", 5, 5);
x_1715 = l_Lean_Name_mkStr2(x_1690, x_1714);
x_1716 = l_Lean_Expr_const___override(x_1715, x_1698);
x_1717 = lean_unsigned_to_nat(12u);
x_1718 = lean_mk_empty_array_with_capacity(x_1717);
x_1719 = lean_array_push(x_1718, x_1652);
x_1720 = lean_array_push(x_1719, x_1655);
x_1721 = lean_array_push(x_1720, x_1658);
x_1722 = lean_array_push(x_1721, x_1618);
x_1723 = lean_array_push(x_1722, x_1641);
x_1724 = lean_array_push(x_1723, x_1687);
x_1725 = lean_array_push(x_1724, x_1713);
x_1726 = lean_array_push(x_1725, x_1619);
x_1727 = lean_array_push(x_1726, x_1620);
x_1728 = lean_array_push(x_1727, x_1643);
x_1729 = lean_array_push(x_1728, x_1);
x_1730 = lean_array_push(x_1729, x_3);
x_1731 = l_Lean_mkAppN(x_1716, x_1730);
lean_dec(x_1730);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1731);
x_1732 = lean_infer_type(x_1731, x_5, x_6, x_7, x_8, x_1712);
if (lean_obj_tag(x_1732) == 0)
{
lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; 
x_1733 = lean_ctor_get(x_1732, 0);
lean_inc(x_1733);
x_1734 = lean_ctor_get(x_1732, 1);
lean_inc(x_1734);
lean_dec(x_1732);
x_1735 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1733, x_6, x_1734);
x_1736 = lean_ctor_get(x_1735, 0);
lean_inc(x_1736);
x_1737 = lean_ctor_get(x_1735, 1);
lean_inc(x_1737);
if (lean_is_exclusive(x_1735)) {
 lean_ctor_release(x_1735, 0);
 lean_ctor_release(x_1735, 1);
 x_1738 = x_1735;
} else {
 lean_dec_ref(x_1735);
 x_1738 = lean_box(0);
}
x_1739 = l_Lean_Expr_headBeta(x_1736);
x_1740 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1739, x_1737);
x_1741 = lean_ctor_get(x_1740, 0);
lean_inc(x_1741);
if (lean_obj_tag(x_1741) == 0)
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; 
lean_dec(x_1731);
lean_dec(x_1644);
x_1742 = lean_ctor_get(x_1740, 1);
lean_inc(x_1742);
lean_dec(x_1740);
x_1743 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_1744 = l_Lean_stringToMessageData(x_1743);
lean_dec(x_1743);
x_1745 = l_Lean_indentExpr(x_1739);
if (lean_is_scalar(x_1738)) {
 x_1746 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1746 = x_1738;
 lean_ctor_set_tag(x_1746, 7);
}
lean_ctor_set(x_1746, 0, x_1744);
lean_ctor_set(x_1746, 1, x_1745);
x_1747 = lean_mk_string_unchecked("", 0, 0);
x_1748 = l_Lean_stringToMessageData(x_1747);
lean_dec(x_1747);
if (lean_is_scalar(x_1625)) {
 x_1749 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1749 = x_1625;
 lean_ctor_set_tag(x_1749, 7);
}
lean_ctor_set(x_1749, 0, x_1746);
lean_ctor_set(x_1749, 1, x_1748);
x_1750 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_1749, x_5, x_6, x_7, x_8, x_1742);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1751 = lean_ctor_get(x_1750, 0);
lean_inc(x_1751);
x_1752 = lean_ctor_get(x_1750, 1);
lean_inc(x_1752);
if (lean_is_exclusive(x_1750)) {
 lean_ctor_release(x_1750, 0);
 lean_ctor_release(x_1750, 1);
 x_1753 = x_1750;
} else {
 lean_dec_ref(x_1750);
 x_1753 = lean_box(0);
}
if (lean_is_scalar(x_1753)) {
 x_1754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1754 = x_1753;
}
lean_ctor_set(x_1754, 0, x_1751);
lean_ctor_set(x_1754, 1, x_1752);
return x_1754;
}
else
{
lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; 
lean_dec(x_1741);
lean_dec(x_1738);
lean_dec(x_1625);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1755 = lean_ctor_get(x_1740, 1);
lean_inc(x_1755);
if (lean_is_exclusive(x_1740)) {
 lean_ctor_release(x_1740, 0);
 lean_ctor_release(x_1740, 1);
 x_1756 = x_1740;
} else {
 lean_dec_ref(x_1740);
 x_1756 = lean_box(0);
}
if (lean_is_scalar(x_1644)) {
 x_1757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1757 = x_1644;
}
lean_ctor_set(x_1757, 0, x_1731);
lean_ctor_set(x_1757, 1, x_1739);
if (lean_is_scalar(x_1756)) {
 x_1758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1758 = x_1756;
}
lean_ctor_set(x_1758, 0, x_1757);
lean_ctor_set(x_1758, 1, x_1755);
return x_1758;
}
}
else
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; 
lean_dec(x_1731);
lean_dec(x_1644);
lean_dec(x_1625);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1759 = lean_ctor_get(x_1732, 0);
lean_inc(x_1759);
x_1760 = lean_ctor_get(x_1732, 1);
lean_inc(x_1760);
if (lean_is_exclusive(x_1732)) {
 lean_ctor_release(x_1732, 0);
 lean_ctor_release(x_1732, 1);
 x_1761 = x_1732;
} else {
 lean_dec_ref(x_1732);
 x_1761 = lean_box(0);
}
if (lean_is_scalar(x_1761)) {
 x_1762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1762 = x_1761;
}
lean_ctor_set(x_1762, 0, x_1759);
lean_ctor_set(x_1762, 1, x_1760);
return x_1762;
}
}
else
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; 
lean_dec(x_1711);
lean_dec(x_1698);
lean_dec(x_1690);
lean_dec(x_1687);
lean_dec(x_1658);
lean_dec(x_1655);
lean_dec(x_1652);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1641);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_dec(x_3);
lean_dec(x_1);
x_1763 = lean_ctor_get(x_1710, 1);
lean_inc(x_1763);
lean_dec(x_1710);
x_1764 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_1765 = l_Lean_stringToMessageData(x_1764);
lean_dec(x_1764);
x_1766 = l_Lean_indentExpr(x_1708);
if (lean_is_scalar(x_1625)) {
 x_1767 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1767 = x_1625;
 lean_ctor_set_tag(x_1767, 7);
}
lean_ctor_set(x_1767, 0, x_1765);
lean_ctor_set(x_1767, 1, x_1766);
x_1768 = lean_mk_string_unchecked("", 0, 0);
x_1769 = l_Lean_stringToMessageData(x_1768);
lean_dec(x_1768);
lean_inc(x_1769);
if (lean_is_scalar(x_1621)) {
 x_1770 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1770 = x_1621;
 lean_ctor_set_tag(x_1770, 7);
}
lean_ctor_set(x_1770, 0, x_1767);
lean_ctor_set(x_1770, 1, x_1769);
x_1771 = l_Lean_useDiagnosticMsg;
x_1772 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1772, 0, x_1770);
lean_ctor_set(x_1772, 1, x_1771);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_1769);
lean_ctor_set(x_10, 0, x_1772);
x_1773 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_10, x_5, x_6, x_7, x_8, x_1763);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1773;
}
}
else
{
lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; 
lean_dec(x_1708);
lean_dec(x_1698);
lean_dec(x_1690);
lean_dec(x_1687);
lean_dec(x_1658);
lean_dec(x_1655);
lean_dec(x_1652);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1641);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1774 = lean_ctor_get(x_1710, 0);
lean_inc(x_1774);
x_1775 = lean_ctor_get(x_1710, 1);
lean_inc(x_1775);
if (lean_is_exclusive(x_1710)) {
 lean_ctor_release(x_1710, 0);
 lean_ctor_release(x_1710, 1);
 x_1776 = x_1710;
} else {
 lean_dec_ref(x_1710);
 x_1776 = lean_box(0);
}
if (lean_is_scalar(x_1776)) {
 x_1777 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1777 = x_1776;
}
lean_ctor_set(x_1777, 0, x_1774);
lean_ctor_set(x_1777, 1, x_1775);
return x_1777;
}
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; 
lean_dec(x_1664);
lean_dec(x_1661);
lean_dec(x_1658);
lean_dec(x_1655);
lean_dec(x_1652);
lean_dec(x_1649);
lean_dec(x_1646);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1642);
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1637);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1778 = lean_ctor_get(x_1666, 0);
lean_inc(x_1778);
x_1779 = lean_ctor_get(x_1666, 1);
lean_inc(x_1779);
if (lean_is_exclusive(x_1666)) {
 lean_ctor_release(x_1666, 0);
 lean_ctor_release(x_1666, 1);
 x_1780 = x_1666;
} else {
 lean_dec_ref(x_1666);
 x_1780 = lean_box(0);
}
if (lean_is_scalar(x_1780)) {
 x_1781 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1781 = x_1780;
}
lean_ctor_set(x_1781, 0, x_1778);
lean_ctor_set(x_1781, 1, x_1779);
return x_1781;
}
}
else
{
lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; 
lean_dec(x_1661);
lean_dec(x_1658);
lean_dec(x_1655);
lean_dec(x_1652);
lean_dec(x_1649);
lean_dec(x_1646);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1642);
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1637);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1782 = lean_ctor_get(x_1663, 0);
lean_inc(x_1782);
x_1783 = lean_ctor_get(x_1663, 1);
lean_inc(x_1783);
if (lean_is_exclusive(x_1663)) {
 lean_ctor_release(x_1663, 0);
 lean_ctor_release(x_1663, 1);
 x_1784 = x_1663;
} else {
 lean_dec_ref(x_1663);
 x_1784 = lean_box(0);
}
if (lean_is_scalar(x_1784)) {
 x_1785 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1785 = x_1784;
}
lean_ctor_set(x_1785, 0, x_1782);
lean_ctor_set(x_1785, 1, x_1783);
return x_1785;
}
}
else
{
lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; 
lean_dec(x_1658);
lean_dec(x_1655);
lean_dec(x_1652);
lean_dec(x_1649);
lean_dec(x_1646);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1642);
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1637);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1786 = lean_ctor_get(x_1660, 0);
lean_inc(x_1786);
x_1787 = lean_ctor_get(x_1660, 1);
lean_inc(x_1787);
if (lean_is_exclusive(x_1660)) {
 lean_ctor_release(x_1660, 0);
 lean_ctor_release(x_1660, 1);
 x_1788 = x_1660;
} else {
 lean_dec_ref(x_1660);
 x_1788 = lean_box(0);
}
if (lean_is_scalar(x_1788)) {
 x_1789 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1789 = x_1788;
}
lean_ctor_set(x_1789, 0, x_1786);
lean_ctor_set(x_1789, 1, x_1787);
return x_1789;
}
}
else
{
lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; 
lean_dec(x_1655);
lean_dec(x_1652);
lean_dec(x_1649);
lean_dec(x_1646);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1642);
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1637);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1790 = lean_ctor_get(x_1657, 0);
lean_inc(x_1790);
x_1791 = lean_ctor_get(x_1657, 1);
lean_inc(x_1791);
if (lean_is_exclusive(x_1657)) {
 lean_ctor_release(x_1657, 0);
 lean_ctor_release(x_1657, 1);
 x_1792 = x_1657;
} else {
 lean_dec_ref(x_1657);
 x_1792 = lean_box(0);
}
if (lean_is_scalar(x_1792)) {
 x_1793 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1793 = x_1792;
}
lean_ctor_set(x_1793, 0, x_1790);
lean_ctor_set(x_1793, 1, x_1791);
return x_1793;
}
}
else
{
lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; 
lean_dec(x_1652);
lean_dec(x_1649);
lean_dec(x_1646);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1642);
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1637);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1794 = lean_ctor_get(x_1654, 0);
lean_inc(x_1794);
x_1795 = lean_ctor_get(x_1654, 1);
lean_inc(x_1795);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 lean_ctor_release(x_1654, 1);
 x_1796 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1796 = lean_box(0);
}
if (lean_is_scalar(x_1796)) {
 x_1797 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1797 = x_1796;
}
lean_ctor_set(x_1797, 0, x_1794);
lean_ctor_set(x_1797, 1, x_1795);
return x_1797;
}
}
else
{
lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; 
lean_dec(x_1649);
lean_dec(x_1646);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1642);
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1637);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1798 = lean_ctor_get(x_1651, 0);
lean_inc(x_1798);
x_1799 = lean_ctor_get(x_1651, 1);
lean_inc(x_1799);
if (lean_is_exclusive(x_1651)) {
 lean_ctor_release(x_1651, 0);
 lean_ctor_release(x_1651, 1);
 x_1800 = x_1651;
} else {
 lean_dec_ref(x_1651);
 x_1800 = lean_box(0);
}
if (lean_is_scalar(x_1800)) {
 x_1801 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1801 = x_1800;
}
lean_ctor_set(x_1801, 0, x_1798);
lean_ctor_set(x_1801, 1, x_1799);
return x_1801;
}
}
else
{
lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; 
lean_dec(x_1646);
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1642);
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1637);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1802 = lean_ctor_get(x_1648, 0);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1648, 1);
lean_inc(x_1803);
if (lean_is_exclusive(x_1648)) {
 lean_ctor_release(x_1648, 0);
 lean_ctor_release(x_1648, 1);
 x_1804 = x_1648;
} else {
 lean_dec_ref(x_1648);
 x_1804 = lean_box(0);
}
if (lean_is_scalar(x_1804)) {
 x_1805 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1805 = x_1804;
}
lean_ctor_set(x_1805, 0, x_1802);
lean_ctor_set(x_1805, 1, x_1803);
return x_1805;
}
}
else
{
lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; 
lean_dec(x_1644);
lean_dec(x_1643);
lean_dec(x_1642);
lean_dec(x_1641);
lean_dec(x_1640);
lean_dec(x_1637);
lean_dec(x_1625);
lean_dec(x_1621);
lean_dec(x_1620);
lean_dec(x_1619);
lean_dec(x_1618);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1806 = lean_ctor_get(x_1645, 0);
lean_inc(x_1806);
x_1807 = lean_ctor_get(x_1645, 1);
lean_inc(x_1807);
if (lean_is_exclusive(x_1645)) {
 lean_ctor_release(x_1645, 0);
 lean_ctor_release(x_1645, 1);
 x_1808 = x_1645;
} else {
 lean_dec_ref(x_1645);
 x_1808 = lean_box(0);
}
if (lean_is_scalar(x_1808)) {
 x_1809 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1809 = x_1808;
}
lean_ctor_set(x_1809, 0, x_1806);
lean_ctor_set(x_1809, 1, x_1807);
return x_1809;
}
}
}
}
else
{
lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; 
x_1810 = lean_ctor_get(x_10, 1);
lean_inc(x_1810);
lean_dec(x_10);
x_1811 = lean_ctor_get(x_20, 0);
lean_inc(x_1811);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_1812 = x_20;
} else {
 lean_dec_ref(x_20);
 x_1812 = lean_box(0);
}
x_1813 = lean_ctor_get(x_21, 0);
lean_inc(x_1813);
x_1814 = lean_ctor_get(x_21, 1);
lean_inc(x_1814);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_1815 = x_21;
} else {
 lean_dec_ref(x_21);
 x_1815 = lean_box(0);
}
x_1816 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_4, x_6, x_1810);
x_1817 = lean_ctor_get(x_1816, 0);
lean_inc(x_1817);
x_1818 = lean_ctor_get(x_1816, 1);
lean_inc(x_1818);
if (lean_is_exclusive(x_1816)) {
 lean_ctor_release(x_1816, 0);
 lean_ctor_release(x_1816, 1);
 x_1819 = x_1816;
} else {
 lean_dec_ref(x_1816);
 x_1819 = lean_box(0);
}
x_1820 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1817, x_1818);
lean_dec(x_1817);
x_1821 = lean_ctor_get(x_1820, 0);
lean_inc(x_1821);
if (lean_obj_tag(x_1821) == 0)
{
lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; 
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_3);
lean_dec(x_1);
x_1822 = lean_ctor_get(x_1820, 1);
lean_inc(x_1822);
lean_dec(x_1820);
x_1823 = lean_mk_string_unchecked("Lean.Elab.Calc", 14, 14);
x_1824 = lean_mk_string_unchecked("Lean.Elab.Term.mkCalcTrans", 26, 26);
x_1825 = lean_unsigned_to_nat(31u);
x_1826 = lean_unsigned_to_nat(72u);
x_1827 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_1828 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1823, x_1824, x_1825, x_1826, x_1827);
lean_dec(x_1827);
lean_dec(x_1824);
lean_dec(x_1823);
x_1829 = l_panic___at___Lean_Elab_Term_mkCalcTrans_spec__0(x_1828, x_5, x_6, x_7, x_8, x_1822);
return x_1829;
}
else
{
lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; 
x_1830 = lean_ctor_get(x_1821, 0);
lean_inc(x_1830);
if (lean_is_exclusive(x_1821)) {
 lean_ctor_release(x_1821, 0);
 x_1831 = x_1821;
} else {
 lean_dec_ref(x_1821);
 x_1831 = lean_box(0);
}
x_1832 = lean_ctor_get(x_1830, 1);
lean_inc(x_1832);
x_1833 = lean_ctor_get(x_1820, 1);
lean_inc(x_1833);
if (lean_is_exclusive(x_1820)) {
 lean_ctor_release(x_1820, 0);
 lean_ctor_release(x_1820, 1);
 x_1834 = x_1820;
} else {
 lean_dec_ref(x_1820);
 x_1834 = lean_box(0);
}
x_1835 = lean_ctor_get(x_1830, 0);
lean_inc(x_1835);
if (lean_is_exclusive(x_1830)) {
 lean_ctor_release(x_1830, 0);
 lean_ctor_release(x_1830, 1);
 x_1836 = x_1830;
} else {
 lean_dec_ref(x_1830);
 x_1836 = lean_box(0);
}
x_1837 = lean_ctor_get(x_1832, 1);
lean_inc(x_1837);
if (lean_is_exclusive(x_1832)) {
 lean_ctor_release(x_1832, 0);
 lean_ctor_release(x_1832, 1);
 x_1838 = x_1832;
} else {
 lean_dec_ref(x_1832);
 x_1838 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1811);
x_1839 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1811, x_5, x_6, x_7, x_8, x_1833);
if (lean_obj_tag(x_1839) == 0)
{
lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; 
x_1840 = lean_ctor_get(x_1839, 0);
lean_inc(x_1840);
x_1841 = lean_ctor_get(x_1839, 1);
lean_inc(x_1841);
lean_dec(x_1839);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1835);
x_1842 = l___private_Lean_Elab_Calc_0__Lean_Elab_Term_getRelUniv(x_1835, x_5, x_6, x_7, x_8, x_1841);
if (lean_obj_tag(x_1842) == 0)
{
lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; 
x_1843 = lean_ctor_get(x_1842, 0);
lean_inc(x_1843);
x_1844 = lean_ctor_get(x_1842, 1);
lean_inc(x_1844);
lean_dec(x_1842);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1813);
x_1845 = lean_infer_type(x_1813, x_5, x_6, x_7, x_8, x_1844);
if (lean_obj_tag(x_1845) == 0)
{
lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; 
x_1846 = lean_ctor_get(x_1845, 0);
lean_inc(x_1846);
x_1847 = lean_ctor_get(x_1845, 1);
lean_inc(x_1847);
lean_dec(x_1845);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1814);
x_1848 = lean_infer_type(x_1814, x_5, x_6, x_7, x_8, x_1847);
if (lean_obj_tag(x_1848) == 0)
{
lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; 
x_1849 = lean_ctor_get(x_1848, 0);
lean_inc(x_1849);
x_1850 = lean_ctor_get(x_1848, 1);
lean_inc(x_1850);
lean_dec(x_1848);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1837);
x_1851 = lean_infer_type(x_1837, x_5, x_6, x_7, x_8, x_1850);
if (lean_obj_tag(x_1851) == 0)
{
lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; 
x_1852 = lean_ctor_get(x_1851, 0);
lean_inc(x_1852);
x_1853 = lean_ctor_get(x_1851, 1);
lean_inc(x_1853);
lean_dec(x_1851);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1846);
x_1854 = l_Lean_Meta_getLevel(x_1846, x_5, x_6, x_7, x_8, x_1853);
if (lean_obj_tag(x_1854) == 0)
{
lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; 
x_1855 = lean_ctor_get(x_1854, 0);
lean_inc(x_1855);
x_1856 = lean_ctor_get(x_1854, 1);
lean_inc(x_1856);
lean_dec(x_1854);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1849);
x_1857 = l_Lean_Meta_getLevel(x_1849, x_5, x_6, x_7, x_8, x_1856);
if (lean_obj_tag(x_1857) == 0)
{
lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; 
x_1858 = lean_ctor_get(x_1857, 0);
lean_inc(x_1858);
x_1859 = lean_ctor_get(x_1857, 1);
lean_inc(x_1859);
lean_dec(x_1857);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1852);
x_1860 = l_Lean_Meta_getLevel(x_1852, x_5, x_6, x_7, x_8, x_1859);
if (lean_obj_tag(x_1860) == 0)
{
lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; uint8_t x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; 
x_1861 = lean_ctor_get(x_1860, 0);
lean_inc(x_1861);
x_1862 = lean_ctor_get(x_1860, 1);
lean_inc(x_1862);
lean_dec(x_1860);
x_1863 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_1862);
x_1864 = lean_ctor_get(x_1863, 0);
lean_inc(x_1864);
x_1865 = lean_ctor_get(x_1863, 1);
lean_inc(x_1865);
if (lean_is_exclusive(x_1863)) {
 lean_ctor_release(x_1863, 0);
 lean_ctor_release(x_1863, 1);
 x_1866 = x_1863;
} else {
 lean_dec_ref(x_1863);
 x_1866 = lean_box(0);
}
lean_inc(x_1864);
x_1867 = l_Lean_Expr_sort___override(x_1864);
lean_inc(x_1852);
x_1868 = l_Lean_mkArrow(x_1852, x_1867, x_7, x_8, x_1865);
x_1869 = lean_ctor_get(x_1868, 0);
lean_inc(x_1869);
x_1870 = lean_ctor_get(x_1868, 1);
lean_inc(x_1870);
if (lean_is_exclusive(x_1868)) {
 lean_ctor_release(x_1868, 0);
 lean_ctor_release(x_1868, 1);
 x_1871 = x_1868;
} else {
 lean_dec_ref(x_1868);
 x_1871 = lean_box(0);
}
lean_inc(x_1846);
x_1872 = l_Lean_mkArrow(x_1846, x_1869, x_7, x_8, x_1870);
x_1873 = lean_ctor_get(x_1872, 0);
lean_inc(x_1873);
x_1874 = lean_ctor_get(x_1872, 1);
lean_inc(x_1874);
if (lean_is_exclusive(x_1872)) {
 lean_ctor_release(x_1872, 0);
 lean_ctor_release(x_1872, 1);
 x_1875 = x_1872;
} else {
 lean_dec_ref(x_1872);
 x_1875 = lean_box(0);
}
if (lean_is_scalar(x_1831)) {
 x_1876 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1876 = x_1831;
}
lean_ctor_set(x_1876, 0, x_1873);
x_1877 = lean_box(0);
x_1878 = lean_box(0);
x_1879 = lean_unbox(x_1877);
lean_inc(x_5);
x_1880 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1876, x_1879, x_1878, x_5, x_6, x_7, x_8, x_1874);
x_1881 = lean_ctor_get(x_1880, 0);
lean_inc(x_1881);
x_1882 = lean_ctor_get(x_1880, 1);
lean_inc(x_1882);
if (lean_is_exclusive(x_1880)) {
 lean_ctor_release(x_1880, 0);
 lean_ctor_release(x_1880, 1);
 x_1883 = x_1880;
} else {
 lean_dec_ref(x_1880);
 x_1883 = lean_box(0);
}
x_1884 = lean_mk_string_unchecked("Trans", 5, 5);
lean_inc(x_1884);
x_1885 = l_Lean_Name_mkStr1(x_1884);
x_1886 = lean_box(0);
if (lean_is_scalar(x_1883)) {
 x_1887 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1887 = x_1883;
 lean_ctor_set_tag(x_1887, 1);
}
lean_ctor_set(x_1887, 0, x_1861);
lean_ctor_set(x_1887, 1, x_1886);
if (lean_is_scalar(x_1875)) {
 x_1888 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1888 = x_1875;
 lean_ctor_set_tag(x_1888, 1);
}
lean_ctor_set(x_1888, 0, x_1858);
lean_ctor_set(x_1888, 1, x_1887);
if (lean_is_scalar(x_1871)) {
 x_1889 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1889 = x_1871;
 lean_ctor_set_tag(x_1889, 1);
}
lean_ctor_set(x_1889, 0, x_1855);
lean_ctor_set(x_1889, 1, x_1888);
if (lean_is_scalar(x_1866)) {
 x_1890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1890 = x_1866;
 lean_ctor_set_tag(x_1890, 1);
}
lean_ctor_set(x_1890, 0, x_1864);
lean_ctor_set(x_1890, 1, x_1889);
if (lean_is_scalar(x_1836)) {
 x_1891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1891 = x_1836;
 lean_ctor_set_tag(x_1891, 1);
}
lean_ctor_set(x_1891, 0, x_1843);
lean_ctor_set(x_1891, 1, x_1890);
if (lean_is_scalar(x_1834)) {
 x_1892 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1892 = x_1834;
 lean_ctor_set_tag(x_1892, 1);
}
lean_ctor_set(x_1892, 0, x_1840);
lean_ctor_set(x_1892, 1, x_1891);
lean_inc(x_1892);
x_1893 = l_Lean_Expr_const___override(x_1885, x_1892);
x_1894 = lean_unsigned_to_nat(6u);
x_1895 = lean_mk_empty_array_with_capacity(x_1894);
lean_inc(x_1846);
x_1896 = lean_array_push(x_1895, x_1846);
lean_inc(x_1849);
x_1897 = lean_array_push(x_1896, x_1849);
lean_inc(x_1852);
x_1898 = lean_array_push(x_1897, x_1852);
lean_inc(x_1811);
x_1899 = lean_array_push(x_1898, x_1811);
lean_inc(x_1835);
x_1900 = lean_array_push(x_1899, x_1835);
lean_inc(x_1881);
x_1901 = lean_array_push(x_1900, x_1881);
x_1902 = l_Lean_mkAppN(x_1893, x_1901);
lean_dec(x_1901);
x_1903 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1902);
x_1904 = l_Lean_Meta_trySynthInstance(x_1902, x_1903, x_5, x_6, x_7, x_8, x_1882);
if (lean_obj_tag(x_1904) == 0)
{
lean_object* x_1905; 
x_1905 = lean_ctor_get(x_1904, 0);
lean_inc(x_1905);
if (lean_obj_tag(x_1905) == 1)
{
lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; 
lean_dec(x_1902);
lean_dec(x_1815);
lean_dec(x_1812);
x_1906 = lean_ctor_get(x_1904, 1);
lean_inc(x_1906);
lean_dec(x_1904);
x_1907 = lean_ctor_get(x_1905, 0);
lean_inc(x_1907);
lean_dec(x_1905);
x_1908 = lean_mk_string_unchecked("trans", 5, 5);
x_1909 = l_Lean_Name_mkStr2(x_1884, x_1908);
x_1910 = l_Lean_Expr_const___override(x_1909, x_1892);
x_1911 = lean_unsigned_to_nat(12u);
x_1912 = lean_mk_empty_array_with_capacity(x_1911);
x_1913 = lean_array_push(x_1912, x_1846);
x_1914 = lean_array_push(x_1913, x_1849);
x_1915 = lean_array_push(x_1914, x_1852);
x_1916 = lean_array_push(x_1915, x_1811);
x_1917 = lean_array_push(x_1916, x_1835);
x_1918 = lean_array_push(x_1917, x_1881);
x_1919 = lean_array_push(x_1918, x_1907);
x_1920 = lean_array_push(x_1919, x_1813);
x_1921 = lean_array_push(x_1920, x_1814);
x_1922 = lean_array_push(x_1921, x_1837);
x_1923 = lean_array_push(x_1922, x_1);
x_1924 = lean_array_push(x_1923, x_3);
x_1925 = l_Lean_mkAppN(x_1910, x_1924);
lean_dec(x_1924);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1925);
x_1926 = lean_infer_type(x_1925, x_5, x_6, x_7, x_8, x_1906);
if (lean_obj_tag(x_1926) == 0)
{
lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; 
x_1927 = lean_ctor_get(x_1926, 0);
lean_inc(x_1927);
x_1928 = lean_ctor_get(x_1926, 1);
lean_inc(x_1928);
lean_dec(x_1926);
x_1929 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1927, x_6, x_1928);
x_1930 = lean_ctor_get(x_1929, 0);
lean_inc(x_1930);
x_1931 = lean_ctor_get(x_1929, 1);
lean_inc(x_1931);
if (lean_is_exclusive(x_1929)) {
 lean_ctor_release(x_1929, 0);
 lean_ctor_release(x_1929, 1);
 x_1932 = x_1929;
} else {
 lean_dec_ref(x_1929);
 x_1932 = lean_box(0);
}
x_1933 = l_Lean_Expr_headBeta(x_1930);
x_1934 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_1933, x_1931);
x_1935 = lean_ctor_get(x_1934, 0);
lean_inc(x_1935);
if (lean_obj_tag(x_1935) == 0)
{
lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; 
lean_dec(x_1925);
lean_dec(x_1838);
x_1936 = lean_ctor_get(x_1934, 1);
lean_inc(x_1936);
lean_dec(x_1934);
x_1937 = lean_mk_string_unchecked("invalid 'calc' step, step result is not a relation", 50, 50);
x_1938 = l_Lean_stringToMessageData(x_1937);
lean_dec(x_1937);
x_1939 = l_Lean_indentExpr(x_1933);
if (lean_is_scalar(x_1932)) {
 x_1940 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1940 = x_1932;
 lean_ctor_set_tag(x_1940, 7);
}
lean_ctor_set(x_1940, 0, x_1938);
lean_ctor_set(x_1940, 1, x_1939);
x_1941 = lean_mk_string_unchecked("", 0, 0);
x_1942 = l_Lean_stringToMessageData(x_1941);
lean_dec(x_1941);
if (lean_is_scalar(x_1819)) {
 x_1943 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1943 = x_1819;
 lean_ctor_set_tag(x_1943, 7);
}
lean_ctor_set(x_1943, 0, x_1940);
lean_ctor_set(x_1943, 1, x_1942);
x_1944 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_1943, x_5, x_6, x_7, x_8, x_1936);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1945 = lean_ctor_get(x_1944, 0);
lean_inc(x_1945);
x_1946 = lean_ctor_get(x_1944, 1);
lean_inc(x_1946);
if (lean_is_exclusive(x_1944)) {
 lean_ctor_release(x_1944, 0);
 lean_ctor_release(x_1944, 1);
 x_1947 = x_1944;
} else {
 lean_dec_ref(x_1944);
 x_1947 = lean_box(0);
}
if (lean_is_scalar(x_1947)) {
 x_1948 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1948 = x_1947;
}
lean_ctor_set(x_1948, 0, x_1945);
lean_ctor_set(x_1948, 1, x_1946);
return x_1948;
}
else
{
lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; 
lean_dec(x_1935);
lean_dec(x_1932);
lean_dec(x_1819);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1949 = lean_ctor_get(x_1934, 1);
lean_inc(x_1949);
if (lean_is_exclusive(x_1934)) {
 lean_ctor_release(x_1934, 0);
 lean_ctor_release(x_1934, 1);
 x_1950 = x_1934;
} else {
 lean_dec_ref(x_1934);
 x_1950 = lean_box(0);
}
if (lean_is_scalar(x_1838)) {
 x_1951 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1951 = x_1838;
}
lean_ctor_set(x_1951, 0, x_1925);
lean_ctor_set(x_1951, 1, x_1933);
if (lean_is_scalar(x_1950)) {
 x_1952 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1952 = x_1950;
}
lean_ctor_set(x_1952, 0, x_1951);
lean_ctor_set(x_1952, 1, x_1949);
return x_1952;
}
}
else
{
lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; 
lean_dec(x_1925);
lean_dec(x_1838);
lean_dec(x_1819);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1953 = lean_ctor_get(x_1926, 0);
lean_inc(x_1953);
x_1954 = lean_ctor_get(x_1926, 1);
lean_inc(x_1954);
if (lean_is_exclusive(x_1926)) {
 lean_ctor_release(x_1926, 0);
 lean_ctor_release(x_1926, 1);
 x_1955 = x_1926;
} else {
 lean_dec_ref(x_1926);
 x_1955 = lean_box(0);
}
if (lean_is_scalar(x_1955)) {
 x_1956 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1956 = x_1955;
}
lean_ctor_set(x_1956, 0, x_1953);
lean_ctor_set(x_1956, 1, x_1954);
return x_1956;
}
}
else
{
lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; 
lean_dec(x_1905);
lean_dec(x_1892);
lean_dec(x_1884);
lean_dec(x_1881);
lean_dec(x_1852);
lean_dec(x_1849);
lean_dec(x_1846);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1835);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1811);
lean_dec(x_3);
lean_dec(x_1);
x_1957 = lean_ctor_get(x_1904, 1);
lean_inc(x_1957);
lean_dec(x_1904);
x_1958 = lean_mk_string_unchecked("invalid 'calc' step, failed to synthesize `Trans` instance", 58, 58);
x_1959 = l_Lean_stringToMessageData(x_1958);
lean_dec(x_1958);
x_1960 = l_Lean_indentExpr(x_1902);
if (lean_is_scalar(x_1819)) {
 x_1961 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1961 = x_1819;
 lean_ctor_set_tag(x_1961, 7);
}
lean_ctor_set(x_1961, 0, x_1959);
lean_ctor_set(x_1961, 1, x_1960);
x_1962 = lean_mk_string_unchecked("", 0, 0);
x_1963 = l_Lean_stringToMessageData(x_1962);
lean_dec(x_1962);
lean_inc(x_1963);
if (lean_is_scalar(x_1815)) {
 x_1964 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1964 = x_1815;
 lean_ctor_set_tag(x_1964, 7);
}
lean_ctor_set(x_1964, 0, x_1961);
lean_ctor_set(x_1964, 1, x_1963);
x_1965 = l_Lean_useDiagnosticMsg;
if (lean_is_scalar(x_1812)) {
 x_1966 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1966 = x_1812;
 lean_ctor_set_tag(x_1966, 7);
}
lean_ctor_set(x_1966, 0, x_1964);
lean_ctor_set(x_1966, 1, x_1965);
x_1967 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1967, 0, x_1966);
lean_ctor_set(x_1967, 1, x_1963);
x_1968 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_1967, x_5, x_6, x_7, x_8, x_1957);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1968;
}
}
else
{
lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; 
lean_dec(x_1902);
lean_dec(x_1892);
lean_dec(x_1884);
lean_dec(x_1881);
lean_dec(x_1852);
lean_dec(x_1849);
lean_dec(x_1846);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1835);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1969 = lean_ctor_get(x_1904, 0);
lean_inc(x_1969);
x_1970 = lean_ctor_get(x_1904, 1);
lean_inc(x_1970);
if (lean_is_exclusive(x_1904)) {
 lean_ctor_release(x_1904, 0);
 lean_ctor_release(x_1904, 1);
 x_1971 = x_1904;
} else {
 lean_dec_ref(x_1904);
 x_1971 = lean_box(0);
}
if (lean_is_scalar(x_1971)) {
 x_1972 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1972 = x_1971;
}
lean_ctor_set(x_1972, 0, x_1969);
lean_ctor_set(x_1972, 1, x_1970);
return x_1972;
}
}
else
{
lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; 
lean_dec(x_1858);
lean_dec(x_1855);
lean_dec(x_1852);
lean_dec(x_1849);
lean_dec(x_1846);
lean_dec(x_1843);
lean_dec(x_1840);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1836);
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_1831);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1973 = lean_ctor_get(x_1860, 0);
lean_inc(x_1973);
x_1974 = lean_ctor_get(x_1860, 1);
lean_inc(x_1974);
if (lean_is_exclusive(x_1860)) {
 lean_ctor_release(x_1860, 0);
 lean_ctor_release(x_1860, 1);
 x_1975 = x_1860;
} else {
 lean_dec_ref(x_1860);
 x_1975 = lean_box(0);
}
if (lean_is_scalar(x_1975)) {
 x_1976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1976 = x_1975;
}
lean_ctor_set(x_1976, 0, x_1973);
lean_ctor_set(x_1976, 1, x_1974);
return x_1976;
}
}
else
{
lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; 
lean_dec(x_1855);
lean_dec(x_1852);
lean_dec(x_1849);
lean_dec(x_1846);
lean_dec(x_1843);
lean_dec(x_1840);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1836);
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_1831);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1977 = lean_ctor_get(x_1857, 0);
lean_inc(x_1977);
x_1978 = lean_ctor_get(x_1857, 1);
lean_inc(x_1978);
if (lean_is_exclusive(x_1857)) {
 lean_ctor_release(x_1857, 0);
 lean_ctor_release(x_1857, 1);
 x_1979 = x_1857;
} else {
 lean_dec_ref(x_1857);
 x_1979 = lean_box(0);
}
if (lean_is_scalar(x_1979)) {
 x_1980 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1980 = x_1979;
}
lean_ctor_set(x_1980, 0, x_1977);
lean_ctor_set(x_1980, 1, x_1978);
return x_1980;
}
}
else
{
lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; 
lean_dec(x_1852);
lean_dec(x_1849);
lean_dec(x_1846);
lean_dec(x_1843);
lean_dec(x_1840);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1836);
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_1831);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1981 = lean_ctor_get(x_1854, 0);
lean_inc(x_1981);
x_1982 = lean_ctor_get(x_1854, 1);
lean_inc(x_1982);
if (lean_is_exclusive(x_1854)) {
 lean_ctor_release(x_1854, 0);
 lean_ctor_release(x_1854, 1);
 x_1983 = x_1854;
} else {
 lean_dec_ref(x_1854);
 x_1983 = lean_box(0);
}
if (lean_is_scalar(x_1983)) {
 x_1984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1984 = x_1983;
}
lean_ctor_set(x_1984, 0, x_1981);
lean_ctor_set(x_1984, 1, x_1982);
return x_1984;
}
}
else
{
lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; 
lean_dec(x_1849);
lean_dec(x_1846);
lean_dec(x_1843);
lean_dec(x_1840);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1836);
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_1831);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1985 = lean_ctor_get(x_1851, 0);
lean_inc(x_1985);
x_1986 = lean_ctor_get(x_1851, 1);
lean_inc(x_1986);
if (lean_is_exclusive(x_1851)) {
 lean_ctor_release(x_1851, 0);
 lean_ctor_release(x_1851, 1);
 x_1987 = x_1851;
} else {
 lean_dec_ref(x_1851);
 x_1987 = lean_box(0);
}
if (lean_is_scalar(x_1987)) {
 x_1988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1988 = x_1987;
}
lean_ctor_set(x_1988, 0, x_1985);
lean_ctor_set(x_1988, 1, x_1986);
return x_1988;
}
}
else
{
lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; 
lean_dec(x_1846);
lean_dec(x_1843);
lean_dec(x_1840);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1836);
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_1831);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1989 = lean_ctor_get(x_1848, 0);
lean_inc(x_1989);
x_1990 = lean_ctor_get(x_1848, 1);
lean_inc(x_1990);
if (lean_is_exclusive(x_1848)) {
 lean_ctor_release(x_1848, 0);
 lean_ctor_release(x_1848, 1);
 x_1991 = x_1848;
} else {
 lean_dec_ref(x_1848);
 x_1991 = lean_box(0);
}
if (lean_is_scalar(x_1991)) {
 x_1992 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1992 = x_1991;
}
lean_ctor_set(x_1992, 0, x_1989);
lean_ctor_set(x_1992, 1, x_1990);
return x_1992;
}
}
else
{
lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; 
lean_dec(x_1843);
lean_dec(x_1840);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1836);
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_1831);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1993 = lean_ctor_get(x_1845, 0);
lean_inc(x_1993);
x_1994 = lean_ctor_get(x_1845, 1);
lean_inc(x_1994);
if (lean_is_exclusive(x_1845)) {
 lean_ctor_release(x_1845, 0);
 lean_ctor_release(x_1845, 1);
 x_1995 = x_1845;
} else {
 lean_dec_ref(x_1845);
 x_1995 = lean_box(0);
}
if (lean_is_scalar(x_1995)) {
 x_1996 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1996 = x_1995;
}
lean_ctor_set(x_1996, 0, x_1993);
lean_ctor_set(x_1996, 1, x_1994);
return x_1996;
}
}
else
{
lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; 
lean_dec(x_1840);
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1836);
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_1831);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_1997 = lean_ctor_get(x_1842, 0);
lean_inc(x_1997);
x_1998 = lean_ctor_get(x_1842, 1);
lean_inc(x_1998);
if (lean_is_exclusive(x_1842)) {
 lean_ctor_release(x_1842, 0);
 lean_ctor_release(x_1842, 1);
 x_1999 = x_1842;
} else {
 lean_dec_ref(x_1842);
 x_1999 = lean_box(0);
}
if (lean_is_scalar(x_1999)) {
 x_2000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2000 = x_1999;
}
lean_ctor_set(x_2000, 0, x_1997);
lean_ctor_set(x_2000, 1, x_1998);
return x_2000;
}
}
else
{
lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; 
lean_dec(x_1838);
lean_dec(x_1837);
lean_dec(x_1836);
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_1831);
lean_dec(x_1819);
lean_dec(x_1815);
lean_dec(x_1814);
lean_dec(x_1813);
lean_dec(x_1812);
lean_dec(x_1811);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_2001 = lean_ctor_get(x_1839, 0);
lean_inc(x_2001);
x_2002 = lean_ctor_get(x_1839, 1);
lean_inc(x_2002);
if (lean_is_exclusive(x_1839)) {
 lean_ctor_release(x_1839, 0);
 lean_ctor_release(x_1839, 1);
 x_2003 = x_1839;
} else {
 lean_dec_ref(x_1839);
 x_2003 = lean_box(0);
}
if (lean_is_scalar(x_2003)) {
 x_2004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2004 = x_2003;
}
lean_ctor_set(x_2004, 0, x_2001);
lean_ctor_set(x_2004, 1, x_2002);
return x_2004;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_mkCalcTrans(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget(x_4, x_3);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_18 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = lean_array_uset(x_4, x_3, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_add(x_3, x_26);
x_28 = lean_array_uset(x_24, x_3, x_21);
x_29 = lean_unbox(x_22);
lean_dec(x_22);
x_3 = x_27;
x_4 = x_28;
x_5 = x_29;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
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
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_array_size(x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(x_1, x_13, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_3 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_box(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = l_Lean_Name_str___override(x_19, x_18);
x_21 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_20, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
case 1:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Lean_Name_str___override(x_19, x_23);
x_25 = l_Lean_Name_str___override(x_24, x_18);
x_26 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_25, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
lean_inc(x_29);
x_30 = l_Lean_Name_str___override(x_19, x_29);
switch (lean_obj_tag(x_28)) {
case 0:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_2);
x_31 = l_Lean_Name_str___override(x_30, x_27);
x_32 = l_Lean_Name_str___override(x_31, x_18);
x_33 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_32, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_33;
}
case 1:
{
lean_object* x_34; 
lean_dec(x_30);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_mk_string_unchecked("Lean", 4, 4);
x_37 = lean_string_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_dec(x_2);
x_38 = l_Lean_Name_str___override(x_19, x_35);
x_39 = l_Lean_Name_str___override(x_38, x_29);
x_40 = l_Lean_Name_str___override(x_39, x_27);
x_41 = l_Lean_Name_str___override(x_40, x_18);
x_42 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_41, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_35);
x_43 = lean_mk_string_unchecked("Parser", 6, 6);
x_44 = lean_string_dec_eq(x_29, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_43);
lean_dec(x_2);
x_45 = l_Lean_Name_str___override(x_19, x_36);
x_46 = l_Lean_Name_str___override(x_45, x_29);
x_47 = l_Lean_Name_str___override(x_46, x_27);
x_48 = l_Lean_Name_str___override(x_47, x_18);
x_49 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_48, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_29);
x_50 = lean_mk_string_unchecked("Term", 4, 4);
x_51 = lean_string_dec_eq(x_27, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_50);
lean_dec(x_2);
x_52 = l_Lean_Name_str___override(x_19, x_36);
x_53 = l_Lean_Name_str___override(x_52, x_43);
x_54 = l_Lean_Name_str___override(x_53, x_27);
x_55 = l_Lean_Name_str___override(x_54, x_18);
x_56 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_55, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_27);
x_57 = lean_mk_string_unchecked("hole", 4, 4);
x_58 = lean_string_dec_eq(x_18, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_2);
x_59 = l_Lean_Name_str___override(x_19, x_36);
x_60 = l_Lean_Name_str___override(x_59, x_43);
x_61 = l_Lean_Name_str___override(x_60, x_50);
x_62 = l_Lean_Name_str___override(x_61, x_18);
x_63 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_62, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_63;
}
else
{
lean_object* x_64; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_inc(x_9);
x_64 = l_Lean_Elab_Term_exprToSyntax(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_9, x_66);
lean_dec(x_9);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_8, 5);
x_71 = lean_box(0);
x_72 = lean_unbox(x_71);
x_73 = l_Lean_SourceInfo_fromRef(x_70, x_72);
x_74 = lean_mk_string_unchecked("typeAscription", 14, 14);
x_75 = l_Lean_Name_mkStr4(x_36, x_43, x_50, x_74);
x_76 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_73);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_73);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked("null", 4, 4);
x_81 = l_Lean_Name_mkStr1(x_80);
lean_inc(x_73);
x_82 = l_Lean_Syntax_node1(x_73, x_81, x_65);
x_83 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_73);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Syntax_node5(x_73, x_75, x_77, x_2, x_79, x_82, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_71);
lean_ctor_set(x_67, 0, x_86);
return x_67;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_87 = lean_ctor_get(x_67, 1);
lean_inc(x_87);
lean_dec(x_67);
x_88 = lean_ctor_get(x_8, 5);
x_89 = lean_box(0);
x_90 = lean_unbox(x_89);
x_91 = l_Lean_SourceInfo_fromRef(x_88, x_90);
x_92 = lean_mk_string_unchecked("typeAscription", 14, 14);
x_93 = l_Lean_Name_mkStr4(x_36, x_43, x_50, x_92);
x_94 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_91);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_91);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked("null", 4, 4);
x_99 = l_Lean_Name_mkStr1(x_98);
lean_inc(x_91);
x_100 = l_Lean_Syntax_node1(x_91, x_99, x_65);
x_101 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_91);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Syntax_node5(x_91, x_93, x_95, x_2, x_97, x_100, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_89);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_87);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_64);
if (x_106 == 0)
{
return x_64;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_64, 0);
x_108 = lean_ctor_get(x_64, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_64);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_2);
x_110 = lean_ctor_get(x_28, 1);
lean_inc(x_110);
lean_dec(x_28);
x_111 = lean_ctor_get(x_34, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_34, 1);
lean_inc(x_112);
lean_dec(x_34);
x_113 = l_Lean_Name_str___override(x_111, x_112);
x_114 = l_Lean_Name_str___override(x_113, x_110);
x_115 = l_Lean_Name_str___override(x_114, x_29);
x_116 = l_Lean_Name_str___override(x_115, x_27);
x_117 = l_Lean_Name_str___override(x_116, x_18);
x_118 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_117, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_118;
}
default: 
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_2);
x_119 = lean_ctor_get(x_28, 1);
lean_inc(x_119);
lean_dec(x_28);
x_120 = lean_ctor_get(x_34, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_34, 1);
lean_inc(x_121);
lean_dec(x_34);
x_122 = l_Lean_Name_num___override(x_120, x_121);
x_123 = l_Lean_Name_str___override(x_122, x_119);
x_124 = l_Lean_Name_str___override(x_123, x_29);
x_125 = l_Lean_Name_str___override(x_124, x_27);
x_126 = l_Lean_Name_str___override(x_125, x_18);
x_127 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_126, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_127;
}
}
}
default: 
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_30);
lean_dec(x_2);
x_128 = lean_ctor_get(x_28, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_28, 1);
lean_inc(x_129);
lean_dec(x_28);
x_130 = l_Lean_Name_num___override(x_128, x_129);
x_131 = l_Lean_Name_str___override(x_130, x_29);
x_132 = l_Lean_Name_str___override(x_131, x_27);
x_133 = l_Lean_Name_str___override(x_132, x_18);
x_134 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_133, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_134;
}
}
}
default: 
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_135 = lean_ctor_get(x_17, 1);
lean_inc(x_135);
lean_dec(x_17);
x_136 = lean_ctor_get(x_22, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_22, 1);
lean_inc(x_137);
lean_dec(x_22);
x_138 = l_Lean_Name_num___override(x_136, x_137);
x_139 = l_Lean_Name_str___override(x_138, x_135);
x_140 = l_Lean_Name_str___override(x_139, x_18);
x_141 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_140, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_141;
}
}
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_2);
x_142 = lean_ctor_get(x_17, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_17, 1);
lean_inc(x_143);
lean_dec(x_17);
x_144 = l_Lean_Name_num___override(x_142, x_143);
x_145 = l_Lean_Name_str___override(x_144, x_18);
x_146 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_15, x_145, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_2, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_2, 2);
lean_inc(x_148);
lean_dec(x_2);
x_149 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_147, x_14, x_148, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_2);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_10);
return x_152;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_annotateFirstHoleWithType_go_spec__0(x_1, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Elab_Term_annotateFirstHoleWithType_go___lam__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Elab_Term_annotateFirstHoleWithType_go(x_2, x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
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
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_annotateFirstHoleWithType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_annotateFirstHoleWithType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_instInhabitedCalcStepView() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("calcFirstStep", 13, 13);
lean_inc(x_5);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_12);
x_13 = l_Lean_Syntax_matchesNull(x_12, x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(2u);
lean_inc(x_12);
x_15 = l_Lean_Syntax_matchesNull(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Syntax_getArg(x_12, x_11);
lean_dec(x_12);
x_18 = l_Lean_Syntax_getArg(x_1, x_10);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_12);
x_21 = lean_st_ref_get(x_3, x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 5);
lean_inc(x_25);
x_26 = l_Lean_replaceRef(x_1, x_25);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_mk_string_unchecked("Parser", 6, 6);
x_29 = lean_mk_string_unchecked("Term", 4, 4);
x_30 = lean_mk_string_unchecked("hole", 4, 4);
x_31 = lean_mk_string_unchecked("_", 1, 1);
x_32 = lean_st_ref_get(x_3, x_23);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_unbox(x_27);
x_36 = l_Lean_SourceInfo_fromRef(x_26, x_35);
lean_dec(x_26);
x_37 = lean_mk_string_unchecked("term_=_", 7, 7);
x_38 = lean_mk_string_unchecked("=", 1, 1);
x_39 = l_Lean_Name_mkStr4(x_5, x_28, x_29, x_30);
lean_inc(x_36);
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 1, x_31);
lean_ctor_set(x_21, 0, x_36);
x_40 = lean_ctor_get(x_2, 10);
lean_inc(x_40);
lean_dec(x_2);
x_41 = l_Lean_Syntax_getArg(x_1, x_10);
x_42 = l_Lean_Name_mkStr1(x_37);
lean_inc(x_36);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_38);
lean_inc(x_36);
x_44 = l_Lean_Syntax_node1(x_36, x_39, x_21);
lean_inc(x_36);
x_45 = l_Lean_Syntax_node3(x_36, x_42, x_41, x_43, x_44);
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec(x_34);
x_47 = l_Lean_Environment_mainModule(x_46);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_48);
x_49 = l_String_toSubstring_x27(x_48);
x_50 = l_Lean_Name_mkStr1(x_48);
lean_inc(x_50);
x_51 = l_Lean_addMacroScope(x_47, x_50, x_40);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_49);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_55);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_45);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_32, 0, x_57);
return x_32;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_58 = lean_ctor_get(x_32, 0);
x_59 = lean_ctor_get(x_32, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_32);
x_60 = lean_unbox(x_27);
x_61 = l_Lean_SourceInfo_fromRef(x_26, x_60);
lean_dec(x_26);
x_62 = lean_mk_string_unchecked("term_=_", 7, 7);
x_63 = lean_mk_string_unchecked("=", 1, 1);
x_64 = l_Lean_Name_mkStr4(x_5, x_28, x_29, x_30);
lean_inc(x_61);
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 1, x_31);
lean_ctor_set(x_21, 0, x_61);
x_65 = lean_ctor_get(x_2, 10);
lean_inc(x_65);
lean_dec(x_2);
x_66 = l_Lean_Syntax_getArg(x_1, x_10);
x_67 = l_Lean_Name_mkStr1(x_62);
lean_inc(x_61);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_63);
lean_inc(x_61);
x_69 = l_Lean_Syntax_node1(x_61, x_64, x_21);
lean_inc(x_61);
x_70 = l_Lean_Syntax_node3(x_61, x_67, x_66, x_68, x_69);
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
lean_dec(x_58);
x_72 = l_Lean_Environment_mainModule(x_71);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_73);
x_74 = l_String_toSubstring_x27(x_73);
x_75 = l_Lean_Name_mkStr1(x_73);
lean_inc(x_75);
x_76 = l_Lean_addMacroScope(x_72, x_75, x_65);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_81, 0, x_61);
lean_ctor_set(x_81, 1, x_74);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_80);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_70);
lean_ctor_set(x_82, 2, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_59);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_84 = lean_ctor_get(x_21, 1);
lean_inc(x_84);
lean_dec(x_21);
x_85 = lean_ctor_get(x_2, 5);
lean_inc(x_85);
x_86 = l_Lean_replaceRef(x_1, x_85);
lean_dec(x_85);
x_87 = lean_box(0);
x_88 = lean_mk_string_unchecked("Parser", 6, 6);
x_89 = lean_mk_string_unchecked("Term", 4, 4);
x_90 = lean_mk_string_unchecked("hole", 4, 4);
x_91 = lean_mk_string_unchecked("_", 1, 1);
x_92 = lean_st_ref_get(x_3, x_84);
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
x_96 = lean_unbox(x_87);
x_97 = l_Lean_SourceInfo_fromRef(x_86, x_96);
lean_dec(x_86);
x_98 = lean_mk_string_unchecked("term_=_", 7, 7);
x_99 = lean_mk_string_unchecked("=", 1, 1);
x_100 = l_Lean_Name_mkStr4(x_5, x_88, x_89, x_90);
lean_inc(x_97);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_91);
x_102 = lean_ctor_get(x_2, 10);
lean_inc(x_102);
lean_dec(x_2);
x_103 = l_Lean_Syntax_getArg(x_1, x_10);
x_104 = l_Lean_Name_mkStr1(x_98);
lean_inc(x_97);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_97);
lean_ctor_set(x_105, 1, x_99);
lean_inc(x_97);
x_106 = l_Lean_Syntax_node1(x_97, x_100, x_101);
lean_inc(x_97);
x_107 = l_Lean_Syntax_node3(x_97, x_104, x_103, x_105, x_106);
x_108 = lean_ctor_get(x_93, 0);
lean_inc(x_108);
lean_dec(x_93);
x_109 = l_Lean_Environment_mainModule(x_108);
lean_dec(x_108);
x_110 = lean_mk_string_unchecked("rfl", 3, 3);
lean_inc(x_110);
x_111 = l_String_toSubstring_x27(x_110);
x_112 = l_Lean_Name_mkStr1(x_110);
lean_inc(x_112);
x_113 = l_Lean_addMacroScope(x_109, x_112, x_102);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_118, 0, x_97);
lean_ctor_set(x_118, 1, x_111);
lean_ctor_set(x_118, 2, x_113);
lean_ctor_set(x_118, 3, x_117);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_1);
lean_ctor_set(x_119, 1, x_107);
lean_ctor_set(x_119, 2, x_118);
if (lean_is_scalar(x_95)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_95;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_94);
return x_120;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_mkCalcFirstStepView___redArg(x_1, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkCalcFirstStepView___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcFirstStepView___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_mkCalcFirstStepView(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("calcStep", 8, 8);
x_17 = l_Lean_Name_mkStr2(x_15, x_16);
x_18 = lean_array_uget(x_1, x_3);
lean_inc(x_18);
x_19 = l_Lean_Syntax_isOfKind(x_18, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_4);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_unsigned_to_nat(2u);
x_27 = l_Lean_Syntax_getArg(x_18, x_26);
x_28 = l_Lean_Syntax_getArg(x_18, x_25);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_array_push(x_4, x_29);
x_6 = x_30;
x_7 = x_5;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_3, x_2);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_mk_string_unchecked("Lean", 4, 4);
x_22 = lean_mk_string_unchecked("calcStep", 8, 8);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = lean_array_uget(x_1, x_3);
lean_inc(x_24);
x_25 = l_Lean_Syntax_isOfKind(x_24, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
lean_dec(x_4);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_11);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_unsigned_to_nat(2u);
x_33 = l_Lean_Syntax_getArg(x_24, x_32);
x_34 = l_Lean_Syntax_getArg(x_24, x_31);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_33);
x_36 = lean_array_push(x_4, x_35);
x_12 = x_36;
x_13 = x_11;
goto block_18;
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___redArg(x_1, x_2, x_16, x_12, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("calcSteps", 9, 9);
lean_inc(x_9);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_mk_string_unchecked("calcFirstStep", 13, 13);
x_17 = l_Lean_Name_mkStr2(x_9, x_16);
lean_inc(x_15);
x_18 = l_Lean_Syntax_isOfKind(x_15, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_8);
return x_19;
}
else
{
lean_object* x_20; 
lean_inc(x_6);
x_20 = l_Lean_Elab_Term_mkCalcFirstStepView___redArg(x_15, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_1);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_23);
x_27 = lean_array_push(x_26, x_21);
x_28 = lean_array_size(x_25);
x_29 = lean_usize_of_nat(x_14);
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0(x_25, x_28, x_29, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_6);
lean_dec(x_25);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_mkCalcStepViews_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkCalcStepViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_mkCalcStepViews(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabCalcSteps_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_26; 
x_26 = lean_usize_dec_lt(x_3, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_28 = lean_array_uget(x_1, x_3);
x_90 = lean_ctor_get(x_4, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_4, 1);
lean_inc(x_91);
lean_dec(x_4);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_28, 1);
lean_inc(x_377);
x_92 = x_377;
x_93 = x_11;
goto block_376;
}
else
{
lean_object* x_378; lean_object* x_379; 
x_378 = lean_ctor_get(x_90, 0);
lean_inc(x_378);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_379 = lean_infer_type(x_378, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_ctor_get(x_28, 1);
lean_inc(x_382);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_383 = l_Lean_Elab_Term_annotateFirstHoleWithType(x_382, x_380, x_5, x_6, x_7, x_8, x_9, x_10, x_381);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_92 = x_384;
x_93 = x_385;
goto block_376;
}
else
{
uint8_t x_386; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_386 = !lean_is_exclusive(x_383);
if (x_386 == 0)
{
return x_383;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_383, 0);
x_388 = lean_ctor_get(x_383, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_383);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
else
{
uint8_t x_390; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_390 = !lean_is_exclusive(x_379);
if (x_390 == 0)
{
return x_379;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_379, 0);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_379);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
block_89:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_28, 2);
lean_inc(x_39);
lean_inc(x_29);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_29);
x_41 = lean_box(0);
x_42 = lean_box(x_26);
x_43 = lean_box(x_26);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 9);
lean_closure_set(x_44, 0, x_39);
lean_closure_set(x_44, 1, x_40);
lean_closure_set(x_44, 2, x_42);
lean_closure_set(x_44, 3, x_43);
lean_closure_set(x_44, 4, x_41);
lean_closure_set(x_44, 5, x_32);
lean_closure_set(x_44, 6, x_33);
lean_closure_set(x_44, 7, x_34);
lean_closure_set(x_44, 8, x_35);
lean_inc(x_37);
x_45 = l_Lean_Core_withFreshMacroScope___redArg(x_44, x_36, x_37, x_38);
if (lean_obj_tag(x_45) == 0)
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_28);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_29);
x_19 = x_30;
x_20 = x_48;
x_21 = x_47;
goto block_25;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_31, 0);
lean_inc(x_49);
lean_dec(x_31);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_54 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_32, x_33, x_34, x_35, x_36, x_37, x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_28, 1);
lean_inc(x_56);
lean_dec(x_28);
x_57 = lean_ctor_get(x_36, 5);
lean_inc(x_57);
x_58 = l_Lean_replaceRef(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
x_59 = lean_ctor_get(x_36, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_36, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_36, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_36, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_36, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_36, 7);
lean_inc(x_65);
x_66 = lean_ctor_get(x_36, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_36, 9);
lean_inc(x_67);
x_68 = lean_ctor_get(x_36, 10);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_36, sizeof(void*)*13);
x_70 = lean_ctor_get(x_36, 11);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_36, sizeof(void*)*13 + 1);
x_72 = lean_ctor_get(x_36, 12);
lean_inc(x_72);
lean_dec(x_36);
x_73 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_61);
lean_ctor_set(x_73, 3, x_62);
lean_ctor_set(x_73, 4, x_63);
lean_ctor_set(x_73, 5, x_58);
lean_ctor_set(x_73, 6, x_64);
lean_ctor_set(x_73, 7, x_65);
lean_ctor_set(x_73, 8, x_66);
lean_ctor_set(x_73, 9, x_67);
lean_ctor_set(x_73, 10, x_68);
lean_ctor_set(x_73, 11, x_70);
lean_ctor_set(x_73, 12, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*13, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*13 + 1, x_71);
x_74 = l_Lean_Elab_Term_mkCalcTrans(x_52, x_53, x_50, x_29, x_34, x_35, x_73, x_37, x_55);
lean_dec(x_53);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_19 = x_30;
x_20 = x_75;
x_21 = x_76;
goto block_25;
}
else
{
uint8_t x_77; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_54);
if (x_81 == 0)
{
return x_54;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_54, 0);
x_83 = lean_ctor_get(x_54, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_54);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_45);
if (x_85 == 0)
{
return x_45;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_45, 0);
x_87 = lean_ctor_get(x_45, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_45);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
block_376:
{
lean_object* x_94; 
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_94 = l_Lean_Elab_Term_elabType(x_92, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_95, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
lean_dec(x_91);
lean_dec(x_90);
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_ctor_get(x_97, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_28, 1);
lean_inc(x_102);
lean_dec(x_28);
x_103 = lean_mk_string_unchecked("invalid 'calc' step, relation expected", 38, 38);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = l_Lean_indentExpr(x_95);
lean_ctor_set_tag(x_97, 7);
lean_ctor_set(x_97, 1, x_105);
lean_ctor_set(x_97, 0, x_104);
x_106 = lean_mk_string_unchecked("", 0, 0);
x_107 = l_Lean_stringToMessageData(x_106);
lean_dec(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_102, x_108, x_5, x_6, x_7, x_8, x_9, x_10, x_100);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_102);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_114 = lean_ctor_get(x_97, 1);
lean_inc(x_114);
lean_dec(x_97);
x_115 = lean_ctor_get(x_28, 1);
lean_inc(x_115);
lean_dec(x_28);
x_116 = lean_mk_string_unchecked("invalid 'calc' step, relation expected", 38, 38);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = l_Lean_indentExpr(x_95);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_mk_string_unchecked("", 0, 0);
x_121 = l_Lean_stringToMessageData(x_120);
lean_dec(x_120);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_115, x_122, x_5, x_6, x_7, x_8, x_9, x_10, x_114);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_115);
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
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_98, 0);
lean_inc(x_128);
lean_dec(x_98);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 1);
x_131 = lean_ctor_get(x_128, 0);
lean_dec(x_131);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_free_object(x_128);
x_132 = lean_ctor_get(x_97, 1);
lean_inc(x_132);
lean_dec(x_97);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = x_95;
x_30 = x_133;
x_31 = x_91;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_132;
goto block_89;
}
else
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_97);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_97, 1);
x_136 = lean_ctor_get(x_97, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_130);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_130, 0);
x_139 = lean_ctor_get(x_130, 1);
x_140 = lean_ctor_get(x_90, 0);
lean_inc(x_140);
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_140);
lean_inc(x_138);
x_141 = l_Lean_Meta_isExprDefEqGuarded(x_138, x_140, x_7, x_8, x_9, x_10, x_135);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_139);
lean_dec(x_95);
lean_dec(x_91);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_138);
x_145 = lean_infer_type(x_138, x_7, x_8, x_9, x_10, x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_140);
x_148 = lean_infer_type(x_140, x_7, x_8, x_9, x_10, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_28, 1);
lean_inc(x_151);
lean_dec(x_28);
x_152 = lean_mk_string_unchecked("invalid 'calc' step, left-hand side is", 38, 38);
x_153 = l_Lean_stringToMessageData(x_152);
lean_dec(x_152);
x_154 = lean_mk_string_unchecked("", 0, 0);
x_155 = l_Lean_stringToMessageData(x_154);
lean_dec(x_154);
x_156 = l_Lean_MessageData_ofExpr(x_138);
lean_inc(x_155);
lean_ctor_set_tag(x_130, 7);
lean_ctor_set(x_130, 1, x_156);
lean_ctor_set(x_130, 0, x_155);
x_157 = lean_mk_string_unchecked(" : ", 3, 3);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
lean_inc(x_158);
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_158);
lean_ctor_set(x_128, 0, x_130);
x_159 = l_Lean_MessageData_ofExpr(x_146);
lean_ctor_set_tag(x_97, 7);
lean_ctor_set(x_97, 1, x_159);
lean_ctor_set(x_97, 0, x_128);
lean_inc(x_155);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_97);
lean_ctor_set(x_160, 1, x_155);
x_161 = l_Lean_indentD(x_160);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_mk_string_unchecked("\nbut previous right-hand side is", 32, 32);
x_164 = l_Lean_stringToMessageData(x_163);
lean_dec(x_163);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_MessageData_ofExpr(x_140);
lean_inc(x_155);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_155);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_158);
x_169 = l_Lean_MessageData_ofExpr(x_149);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
lean_inc(x_155);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_155);
x_172 = l_Lean_indentD(x_171);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_165);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_155);
x_175 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_151, x_174, x_5, x_6, x_7, x_8, x_9, x_10, x_150);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_151);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
return x_175;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_175);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
else
{
uint8_t x_180; 
lean_dec(x_146);
lean_dec(x_140);
lean_free_object(x_130);
lean_dec(x_138);
lean_free_object(x_97);
lean_free_object(x_128);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_180 = !lean_is_exclusive(x_148);
if (x_180 == 0)
{
return x_148;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_148, 0);
x_182 = lean_ctor_get(x_148, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_148);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_140);
lean_free_object(x_130);
lean_dec(x_138);
lean_free_object(x_97);
lean_free_object(x_128);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_184 = !lean_is_exclusive(x_145);
if (x_184 == 0)
{
return x_145;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_145, 0);
x_186 = lean_ctor_get(x_145, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_145);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; 
lean_dec(x_140);
lean_free_object(x_130);
lean_dec(x_138);
lean_free_object(x_97);
lean_free_object(x_128);
x_188 = lean_ctor_get(x_141, 1);
lean_inc(x_188);
lean_dec(x_141);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = x_95;
x_30 = x_139;
x_31 = x_91;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_188;
goto block_89;
}
}
else
{
uint8_t x_189; 
lean_dec(x_140);
lean_free_object(x_130);
lean_dec(x_139);
lean_dec(x_138);
lean_free_object(x_97);
lean_free_object(x_128);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_189 = !lean_is_exclusive(x_141);
if (x_189 == 0)
{
return x_141;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_141, 0);
x_191 = lean_ctor_get(x_141, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_141);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_130, 0);
x_194 = lean_ctor_get(x_130, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_130);
x_195 = lean_ctor_get(x_90, 0);
lean_inc(x_195);
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_195);
lean_inc(x_193);
x_196 = l_Lean_Meta_isExprDefEqGuarded(x_193, x_195, x_7, x_8, x_9, x_10, x_135);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_unbox(x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_194);
lean_dec(x_95);
lean_dec(x_91);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_193);
x_200 = lean_infer_type(x_193, x_7, x_8, x_9, x_10, x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_195);
x_203 = lean_infer_type(x_195, x_7, x_8, x_9, x_10, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_28, 1);
lean_inc(x_206);
lean_dec(x_28);
x_207 = lean_mk_string_unchecked("invalid 'calc' step, left-hand side is", 38, 38);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
x_209 = lean_mk_string_unchecked("", 0, 0);
x_210 = l_Lean_stringToMessageData(x_209);
lean_dec(x_209);
x_211 = l_Lean_MessageData_ofExpr(x_193);
lean_inc(x_210);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_mk_string_unchecked(" : ", 3, 3);
x_214 = l_Lean_stringToMessageData(x_213);
lean_dec(x_213);
lean_inc(x_214);
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_214);
lean_ctor_set(x_128, 0, x_212);
x_215 = l_Lean_MessageData_ofExpr(x_201);
lean_ctor_set_tag(x_97, 7);
lean_ctor_set(x_97, 1, x_215);
lean_ctor_set(x_97, 0, x_128);
lean_inc(x_210);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_97);
lean_ctor_set(x_216, 1, x_210);
x_217 = l_Lean_indentD(x_216);
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_208);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_mk_string_unchecked("\nbut previous right-hand side is", 32, 32);
x_220 = l_Lean_stringToMessageData(x_219);
lean_dec(x_219);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_MessageData_ofExpr(x_195);
lean_inc(x_210);
x_223 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_223, 0, x_210);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_214);
x_225 = l_Lean_MessageData_ofExpr(x_204);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_210);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_210);
x_228 = l_Lean_indentD(x_227);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_221);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_210);
x_231 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_206, x_230, x_5, x_6, x_7, x_8, x_9, x_10, x_205);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_206);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_201);
lean_dec(x_195);
lean_dec(x_193);
lean_free_object(x_97);
lean_free_object(x_128);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_236 = lean_ctor_get(x_203, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_203, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_238 = x_203;
} else {
 lean_dec_ref(x_203);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_195);
lean_dec(x_193);
lean_free_object(x_97);
lean_free_object(x_128);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_240 = lean_ctor_get(x_200, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_200, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_242 = x_200;
} else {
 lean_dec_ref(x_200);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; 
lean_dec(x_195);
lean_dec(x_193);
lean_free_object(x_97);
lean_free_object(x_128);
x_244 = lean_ctor_get(x_196, 1);
lean_inc(x_244);
lean_dec(x_196);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = x_95;
x_30 = x_194;
x_31 = x_91;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_244;
goto block_89;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_free_object(x_97);
lean_free_object(x_128);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_245 = lean_ctor_get(x_196, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_196, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_247 = x_196;
} else {
 lean_dec_ref(x_196);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_97, 1);
lean_inc(x_249);
lean_dec(x_97);
x_250 = lean_ctor_get(x_130, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_130, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_252 = x_130;
} else {
 lean_dec_ref(x_130);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_90, 0);
lean_inc(x_253);
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_253);
lean_inc(x_250);
x_254 = l_Lean_Meta_isExprDefEqGuarded(x_250, x_253, x_7, x_8, x_9, x_10, x_249);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_251);
lean_dec(x_95);
lean_dec(x_91);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_250);
x_258 = lean_infer_type(x_250, x_7, x_8, x_9, x_10, x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_253);
x_261 = lean_infer_type(x_253, x_7, x_8, x_9, x_10, x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_ctor_get(x_28, 1);
lean_inc(x_264);
lean_dec(x_28);
x_265 = lean_mk_string_unchecked("invalid 'calc' step, left-hand side is", 38, 38);
x_266 = l_Lean_stringToMessageData(x_265);
lean_dec(x_265);
x_267 = lean_mk_string_unchecked("", 0, 0);
x_268 = l_Lean_stringToMessageData(x_267);
lean_dec(x_267);
x_269 = l_Lean_MessageData_ofExpr(x_250);
lean_inc(x_268);
if (lean_is_scalar(x_252)) {
 x_270 = lean_alloc_ctor(7, 2, 0);
} else {
 x_270 = x_252;
 lean_ctor_set_tag(x_270, 7);
}
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_mk_string_unchecked(" : ", 3, 3);
x_272 = l_Lean_stringToMessageData(x_271);
lean_dec(x_271);
lean_inc(x_272);
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_272);
lean_ctor_set(x_128, 0, x_270);
x_273 = l_Lean_MessageData_ofExpr(x_259);
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_128);
lean_ctor_set(x_274, 1, x_273);
lean_inc(x_268);
x_275 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_268);
x_276 = l_Lean_indentD(x_275);
x_277 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_277, 0, x_266);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_mk_string_unchecked("\nbut previous right-hand side is", 32, 32);
x_279 = l_Lean_stringToMessageData(x_278);
lean_dec(x_278);
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_279);
x_281 = l_Lean_MessageData_ofExpr(x_253);
lean_inc(x_268);
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_268);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_272);
x_284 = l_Lean_MessageData_ofExpr(x_262);
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
lean_inc(x_268);
x_286 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_268);
x_287 = l_Lean_indentD(x_286);
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_280);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_268);
x_290 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_264, x_289, x_5, x_6, x_7, x_8, x_9, x_10, x_263);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_264);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_293 = x_290;
} else {
 lean_dec_ref(x_290);
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
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_259);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_free_object(x_128);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_295 = lean_ctor_get(x_261, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_261, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_297 = x_261;
} else {
 lean_dec_ref(x_261);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_free_object(x_128);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_299 = lean_ctor_get(x_258, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_258, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_301 = x_258;
} else {
 lean_dec_ref(x_258);
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
else
{
lean_object* x_303; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_free_object(x_128);
x_303 = lean_ctor_get(x_254, 1);
lean_inc(x_303);
lean_dec(x_254);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = x_95;
x_30 = x_251;
x_31 = x_91;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_303;
goto block_89;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_free_object(x_128);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_304 = lean_ctor_get(x_254, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_254, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_306 = x_254;
} else {
 lean_dec_ref(x_254);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
}
}
else
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_128, 1);
lean_inc(x_308);
lean_dec(x_128);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_97, 1);
lean_inc(x_309);
lean_dec(x_97);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = x_95;
x_30 = x_310;
x_31 = x_91;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_309;
goto block_89;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_311 = lean_ctor_get(x_97, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_312 = x_97;
} else {
 lean_dec_ref(x_97);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_308, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_308, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_315 = x_308;
} else {
 lean_dec_ref(x_308);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_90, 0);
lean_inc(x_316);
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_316);
lean_inc(x_313);
x_317 = l_Lean_Meta_isExprDefEqGuarded(x_313, x_316, x_7, x_8, x_9, x_10, x_311);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_unbox(x_318);
lean_dec(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_314);
lean_dec(x_95);
lean_dec(x_91);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_313);
x_321 = lean_infer_type(x_313, x_7, x_8, x_9, x_10, x_320);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_316);
x_324 = lean_infer_type(x_316, x_7, x_8, x_9, x_10, x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_ctor_get(x_28, 1);
lean_inc(x_327);
lean_dec(x_28);
x_328 = lean_mk_string_unchecked("invalid 'calc' step, left-hand side is", 38, 38);
x_329 = l_Lean_stringToMessageData(x_328);
lean_dec(x_328);
x_330 = lean_mk_string_unchecked("", 0, 0);
x_331 = l_Lean_stringToMessageData(x_330);
lean_dec(x_330);
x_332 = l_Lean_MessageData_ofExpr(x_313);
lean_inc(x_331);
if (lean_is_scalar(x_315)) {
 x_333 = lean_alloc_ctor(7, 2, 0);
} else {
 x_333 = x_315;
 lean_ctor_set_tag(x_333, 7);
}
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_mk_string_unchecked(" : ", 3, 3);
x_335 = l_Lean_stringToMessageData(x_334);
lean_dec(x_334);
lean_inc(x_335);
x_336 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_335);
x_337 = l_Lean_MessageData_ofExpr(x_322);
if (lean_is_scalar(x_312)) {
 x_338 = lean_alloc_ctor(7, 2, 0);
} else {
 x_338 = x_312;
 lean_ctor_set_tag(x_338, 7);
}
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
lean_inc(x_331);
x_339 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
x_340 = l_Lean_indentD(x_339);
x_341 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_341, 0, x_329);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_mk_string_unchecked("\nbut previous right-hand side is", 32, 32);
x_343 = l_Lean_stringToMessageData(x_342);
lean_dec(x_342);
x_344 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_343);
x_345 = l_Lean_MessageData_ofExpr(x_316);
lean_inc(x_331);
x_346 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_346, 0, x_331);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_335);
x_348 = l_Lean_MessageData_ofExpr(x_325);
x_349 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
lean_inc(x_331);
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_331);
x_351 = l_Lean_indentD(x_350);
x_352 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_331);
x_354 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_327, x_353, x_5, x_6, x_7, x_8, x_9, x_10, x_326);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_327);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_357 = x_354;
} else {
 lean_dec_ref(x_354);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_322);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_359 = lean_ctor_get(x_324, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_324, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_361 = x_324;
} else {
 lean_dec_ref(x_324);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_363 = lean_ctor_get(x_321, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_321, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_365 = x_321;
} else {
 lean_dec_ref(x_321);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
lean_object* x_367; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_313);
lean_dec(x_312);
x_367 = lean_ctor_get(x_317, 1);
lean_inc(x_367);
lean_dec(x_317);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = x_95;
x_30 = x_314;
x_31 = x_91;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
x_38 = x_367;
goto block_89;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_368 = lean_ctor_get(x_317, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_317, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_370 = x_317;
} else {
 lean_dec_ref(x_317);
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
}
else
{
uint8_t x_372; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_372 = !lean_is_exclusive(x_94);
if (x_372 == 0)
{
return x_94;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_94, 0);
x_374 = lean_ctor_get(x_94, 1);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_94);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
return x_375;
}
}
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_12;
x_11 = x_13;
goto _start;
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_12 = x_24;
x_13 = x_21;
goto block_18;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_elabCalcSteps_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_panic_fn(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; 
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_array_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabCalcSteps_spec__0(x_1, x_12, x_14, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_23 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_24 = lean_unsigned_to_nat(21u);
x_25 = lean_unsigned_to_nat(14u);
x_26 = lean_mk_string_unchecked("value is none", 13, 13);
x_27 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_22, x_23, x_24, x_25, x_26);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_28 = l_panic___at___Lean_Elab_Term_elabCalcSteps_spec__1(x_27);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_31 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_32 = lean_unsigned_to_nat(21u);
x_33 = lean_unsigned_to_nat(14u);
x_34 = lean_mk_string_unchecked("value is none", 13, 13);
x_35 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_34);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_36 = l_panic___at___Lean_Elab_Term_elabCalcSteps_spec__1(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_19, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_18, 0);
lean_inc(x_40);
lean_dec(x_18);
lean_ctor_set(x_19, 0, x_40);
return x_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_ctor_get(x_18, 0);
lean_inc(x_42);
lean_dec(x_18);
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
lean_dec(x_18);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_15, 0);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_15);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabCalcSteps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_elabCalcSteps_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalcSteps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabCalcSteps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_abortTermExceptionId;
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0___redArg(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(2);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__0(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_mk_string_unchecked("'calc' expression", 17, 17);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_MessageData_ofFormat(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Term_throwTypeMismatchError(lean_box(0), x_13, x_1, x_2, x_3, x_14, x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = lean_infer_type(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_21, x_5, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Expr_headBeta(x_24);
x_28 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_27, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_mk_string_unchecked("Lean.Elab.Calc", 14, 14);
x_32 = lean_mk_string_unchecked("Lean.Elab.Term.throwCalcFailure", 31, 31);
x_33 = lean_unsigned_to_nat(129u);
x_34 = lean_unsigned_to_nat(57u);
x_35 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_36 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_31, x_32, x_33, x_34, x_35);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
x_37 = l_panic___at___Lean_Meta_throwLetTypeMismatchMessage_spec__0___redArg(x_36, x_4, x_5, x_6, x_7, x_30);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_41 = x_28;
} else {
 lean_dec_ref(x_28);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_46 = x_39;
} else {
 lean_dec_ref(x_39);
 x_46 = lean_box(0);
}
x_47 = l_Lean_Elab_Term_getCalcRelation_x3f___redArg(x_2, x_40);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_26);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_51 = l_Lean_Elab_Term_throwCalcFailure___redArg___lam__0(x_2, x_27, x_3, x_50, x_4, x_5, x_6, x_7, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_232; 
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_55 = x_47;
} else {
 lean_dec_ref(x_47);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_57 = x_52;
} else {
 lean_dec_ref(x_52);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_232 = l_Lean_Meta_isExprDefEqGuarded(x_42, x_56, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_unbox(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_dec(x_232);
x_236 = lean_box(0);
x_237 = l_Lean_Elab_Term_throwCalcFailure___redArg___lam__0(x_2, x_27, x_3, x_236, x_4, x_5, x_6, x_7, x_235);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_232, 1);
lean_inc(x_238);
lean_dec(x_232);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_58);
lean_inc(x_44);
x_239 = l_Lean_Meta_isExprDefEqGuarded(x_44, x_58, x_4, x_5, x_6, x_7, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_unbox(x_240);
lean_dec(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
lean_dec(x_239);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_243 = l_Lean_Meta_addPPExplicitToExposeDiff(x_44, x_58, x_4, x_5, x_6, x_7, x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = !lean_is_exclusive(x_244);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_244, 0);
x_248 = lean_ctor_get(x_244, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_247);
x_249 = lean_infer_type(x_247, x_4, x_5, x_6, x_7, x_245);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_248);
x_252 = lean_infer_type(x_248, x_4, x_5, x_6, x_7, x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_255 = l_Lean_Meta_addPPExplicitToExposeDiff(x_250, x_253, x_4, x_5, x_6, x_7, x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = !lean_is_exclusive(x_256);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_259 = lean_ctor_get(x_256, 0);
x_260 = lean_ctor_get(x_256, 1);
x_261 = l_Lean_Elab_Term_instInhabitedCalcStepView;
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_array_get(x_261, x_1, x_262);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_mk_string_unchecked("invalid 'calc' step, left-hand side is", 38, 38);
x_266 = l_Lean_stringToMessageData(x_265);
lean_dec(x_265);
x_267 = lean_mk_string_unchecked("", 0, 0);
x_268 = l_Lean_stringToMessageData(x_267);
lean_dec(x_267);
x_269 = l_Lean_MessageData_ofExpr(x_247);
lean_inc(x_268);
lean_ctor_set_tag(x_256, 7);
lean_ctor_set(x_256, 1, x_269);
lean_ctor_set(x_256, 0, x_268);
x_270 = lean_mk_string_unchecked(" : ", 3, 3);
x_271 = l_Lean_stringToMessageData(x_270);
lean_dec(x_270);
lean_inc(x_271);
lean_ctor_set_tag(x_244, 7);
lean_ctor_set(x_244, 1, x_271);
lean_ctor_set(x_244, 0, x_256);
x_272 = l_Lean_MessageData_ofExpr(x_259);
x_273 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_273, 0, x_244);
lean_ctor_set(x_273, 1, x_272);
lean_inc(x_268);
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_268);
x_275 = l_Lean_indentD(x_274);
x_276 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_276, 0, x_266);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_mk_string_unchecked("\nbut is expected to be", 22, 22);
x_278 = l_Lean_stringToMessageData(x_277);
lean_dec(x_277);
x_279 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Lean_MessageData_ofExpr(x_248);
lean_inc(x_268);
x_281 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_281, 0, x_268);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_271);
x_283 = l_Lean_MessageData_ofExpr(x_260);
x_284 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
lean_inc(x_268);
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_268);
x_286 = l_Lean_indentD(x_285);
x_287 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_287, 0, x_279);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_268);
lean_inc(x_6);
x_289 = l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(x_264, x_288, x_4, x_5, x_6, x_7, x_257);
lean_dec(x_264);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_unbox(x_233);
lean_dec(x_233);
x_61 = x_291;
x_62 = x_4;
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_290;
goto block_231;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_292 = lean_ctor_get(x_256, 0);
x_293 = lean_ctor_get(x_256, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_256);
x_294 = l_Lean_Elab_Term_instInhabitedCalcStepView;
x_295 = lean_unsigned_to_nat(0u);
x_296 = lean_array_get(x_294, x_1, x_295);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_298 = lean_mk_string_unchecked("invalid 'calc' step, left-hand side is", 38, 38);
x_299 = l_Lean_stringToMessageData(x_298);
lean_dec(x_298);
x_300 = lean_mk_string_unchecked("", 0, 0);
x_301 = l_Lean_stringToMessageData(x_300);
lean_dec(x_300);
x_302 = l_Lean_MessageData_ofExpr(x_247);
lean_inc(x_301);
x_303 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_mk_string_unchecked(" : ", 3, 3);
x_305 = l_Lean_stringToMessageData(x_304);
lean_dec(x_304);
lean_inc(x_305);
lean_ctor_set_tag(x_244, 7);
lean_ctor_set(x_244, 1, x_305);
lean_ctor_set(x_244, 0, x_303);
x_306 = l_Lean_MessageData_ofExpr(x_292);
x_307 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_307, 0, x_244);
lean_ctor_set(x_307, 1, x_306);
lean_inc(x_301);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_301);
x_309 = l_Lean_indentD(x_308);
x_310 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_310, 0, x_299);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_mk_string_unchecked("\nbut is expected to be", 22, 22);
x_312 = l_Lean_stringToMessageData(x_311);
lean_dec(x_311);
x_313 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_312);
x_314 = l_Lean_MessageData_ofExpr(x_248);
lean_inc(x_301);
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_301);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_305);
x_317 = l_Lean_MessageData_ofExpr(x_293);
x_318 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
lean_inc(x_301);
x_319 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_301);
x_320 = l_Lean_indentD(x_319);
x_321 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_321, 0, x_313);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_301);
lean_inc(x_6);
x_323 = l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(x_297, x_322, x_4, x_5, x_6, x_7, x_257);
lean_dec(x_297);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
lean_dec(x_323);
x_325 = lean_unbox(x_233);
lean_dec(x_233);
x_61 = x_325;
x_62 = x_4;
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_324;
goto block_231;
}
}
else
{
uint8_t x_326; 
lean_free_object(x_244);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_326 = !lean_is_exclusive(x_255);
if (x_326 == 0)
{
return x_255;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_255, 0);
x_328 = lean_ctor_get(x_255, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_255);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
else
{
uint8_t x_330; 
lean_dec(x_250);
lean_free_object(x_244);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_330 = !lean_is_exclusive(x_252);
if (x_330 == 0)
{
return x_252;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_252, 0);
x_332 = lean_ctor_get(x_252, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_252);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
uint8_t x_334; 
lean_free_object(x_244);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_334 = !lean_is_exclusive(x_249);
if (x_334 == 0)
{
return x_249;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_249, 0);
x_336 = lean_ctor_get(x_249, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_249);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_244, 0);
x_339 = lean_ctor_get(x_244, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_244);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_338);
x_340 = lean_infer_type(x_338, x_4, x_5, x_6, x_7, x_245);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_339);
x_343 = lean_infer_type(x_339, x_4, x_5, x_6, x_7, x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_346 = l_Lean_Meta_addPPExplicitToExposeDiff(x_341, x_344, x_4, x_5, x_6, x_7, x_345);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_351 = x_347;
} else {
 lean_dec_ref(x_347);
 x_351 = lean_box(0);
}
x_352 = l_Lean_Elab_Term_instInhabitedCalcStepView;
x_353 = lean_unsigned_to_nat(0u);
x_354 = lean_array_get(x_352, x_1, x_353);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec(x_354);
x_356 = lean_mk_string_unchecked("invalid 'calc' step, left-hand side is", 38, 38);
x_357 = l_Lean_stringToMessageData(x_356);
lean_dec(x_356);
x_358 = lean_mk_string_unchecked("", 0, 0);
x_359 = l_Lean_stringToMessageData(x_358);
lean_dec(x_358);
x_360 = l_Lean_MessageData_ofExpr(x_338);
lean_inc(x_359);
if (lean_is_scalar(x_351)) {
 x_361 = lean_alloc_ctor(7, 2, 0);
} else {
 x_361 = x_351;
 lean_ctor_set_tag(x_361, 7);
}
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_mk_string_unchecked(" : ", 3, 3);
x_363 = l_Lean_stringToMessageData(x_362);
lean_dec(x_362);
lean_inc(x_363);
x_364 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_363);
x_365 = l_Lean_MessageData_ofExpr(x_349);
x_366 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
lean_inc(x_359);
x_367 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_359);
x_368 = l_Lean_indentD(x_367);
x_369 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_369, 0, x_357);
lean_ctor_set(x_369, 1, x_368);
x_370 = lean_mk_string_unchecked("\nbut is expected to be", 22, 22);
x_371 = l_Lean_stringToMessageData(x_370);
lean_dec(x_370);
x_372 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Lean_MessageData_ofExpr(x_339);
lean_inc(x_359);
x_374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_374, 0, x_359);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_363);
x_376 = l_Lean_MessageData_ofExpr(x_350);
x_377 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
lean_inc(x_359);
x_378 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_359);
x_379 = l_Lean_indentD(x_378);
x_380 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_380, 0, x_372);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_359);
lean_inc(x_6);
x_382 = l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(x_355, x_381, x_4, x_5, x_6, x_7, x_348);
lean_dec(x_355);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_384 = lean_unbox(x_233);
lean_dec(x_233);
x_61 = x_384;
x_62 = x_4;
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_383;
goto block_231;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_385 = lean_ctor_get(x_346, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_346, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_387 = x_346;
} else {
 lean_dec_ref(x_346);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_341);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_389 = lean_ctor_get(x_343, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_343, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_391 = x_343;
} else {
 lean_dec_ref(x_343);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_393 = lean_ctor_get(x_340, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_340, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_395 = x_340;
} else {
 lean_dec_ref(x_340);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_397 = !lean_is_exclusive(x_243);
if (x_397 == 0)
{
return x_243;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_243, 0);
x_399 = lean_ctor_get(x_243, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_243);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
lean_object* x_401; lean_object* x_402; uint8_t x_403; 
lean_dec(x_233);
lean_dec(x_58);
lean_dec(x_44);
x_401 = lean_ctor_get(x_239, 1);
lean_inc(x_401);
lean_dec(x_239);
x_402 = lean_box(0);
x_403 = lean_unbox(x_402);
x_61 = x_403;
x_62 = x_4;
x_63 = x_5;
x_64 = x_6;
x_65 = x_7;
x_66 = x_401;
goto block_231;
}
}
else
{
uint8_t x_404; 
lean_dec(x_233);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_404 = !lean_is_exclusive(x_239);
if (x_404 == 0)
{
return x_239;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_239, 0);
x_406 = lean_ctor_get(x_239, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_239);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_408 = !lean_is_exclusive(x_232);
if (x_408 == 0)
{
return x_232;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_232, 0);
x_410 = lean_ctor_get(x_232, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_232);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
block_231:
{
lean_object* x_67; 
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_59);
lean_inc(x_45);
x_67 = l_Lean_Meta_isExprDefEqGuarded(x_45, x_59, x_62, x_63, x_64, x_65, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_71 = l_Lean_Meta_addPPExplicitToExposeDiff(x_45, x_59, x_62, x_63, x_64, x_65, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_75);
x_77 = lean_infer_type(x_75, x_62, x_63, x_64, x_65, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_76);
x_80 = lean_infer_type(x_76, x_62, x_63, x_64, x_65, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_83 = l_Lean_Meta_addPPExplicitToExposeDiff(x_78, x_81, x_62, x_63, x_64, x_65, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
x_89 = l_Lean_Elab_Term_instInhabitedCalcStepView;
x_90 = l_Array_back_x21(lean_box(0), x_89, x_1);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_mk_string_unchecked("invalid 'calc' step, right-hand side is", 39, 39);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = l_Lean_MessageData_ofExpr(x_75);
lean_inc(x_95);
lean_ctor_set_tag(x_84, 7);
lean_ctor_set(x_84, 1, x_96);
lean_ctor_set(x_84, 0, x_95);
x_97 = lean_mk_string_unchecked(" : ", 3, 3);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
lean_inc(x_98);
lean_ctor_set_tag(x_72, 7);
lean_ctor_set(x_72, 1, x_98);
lean_ctor_set(x_72, 0, x_84);
x_99 = l_Lean_MessageData_ofExpr(x_87);
if (lean_is_scalar(x_60)) {
 x_100 = lean_alloc_ctor(7, 2, 0);
} else {
 x_100 = x_60;
 lean_ctor_set_tag(x_100, 7);
}
lean_ctor_set(x_100, 0, x_72);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_95);
if (lean_is_scalar(x_57)) {
 x_101 = lean_alloc_ctor(7, 2, 0);
} else {
 x_101 = x_57;
 lean_ctor_set_tag(x_101, 7);
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_95);
x_102 = l_Lean_indentD(x_101);
if (lean_is_scalar(x_55)) {
 x_103 = lean_alloc_ctor(7, 2, 0);
} else {
 x_103 = x_55;
 lean_ctor_set_tag(x_103, 7);
}
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked("\nbut is expected to be", 22, 22);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
if (lean_is_scalar(x_46)) {
 x_106 = lean_alloc_ctor(7, 2, 0);
} else {
 x_106 = x_46;
 lean_ctor_set_tag(x_106, 7);
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_MessageData_ofExpr(x_76);
lean_inc(x_95);
if (lean_is_scalar(x_43)) {
 x_108 = lean_alloc_ctor(7, 2, 0);
} else {
 x_108 = x_43;
 lean_ctor_set_tag(x_108, 7);
}
lean_ctor_set(x_108, 0, x_95);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_41)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_41;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_98);
x_110 = l_Lean_MessageData_ofExpr(x_88);
if (lean_is_scalar(x_26)) {
 x_111 = lean_alloc_ctor(7, 2, 0);
} else {
 x_111 = x_26;
 lean_ctor_set_tag(x_111, 7);
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_inc(x_95);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_95);
x_113 = l_Lean_indentD(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_95);
lean_inc(x_64);
x_116 = l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(x_91, x_115, x_62, x_63, x_64, x_65, x_85);
lean_dec(x_91);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_9 = x_62;
x_10 = x_63;
x_11 = x_64;
x_12 = x_65;
x_13 = x_117;
goto block_19;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_118 = lean_ctor_get(x_84, 0);
x_119 = lean_ctor_get(x_84, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_84);
x_120 = l_Lean_Elab_Term_instInhabitedCalcStepView;
x_121 = l_Array_back_x21(lean_box(0), x_120, x_1);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_mk_string_unchecked("invalid 'calc' step, right-hand side is", 39, 39);
x_124 = l_Lean_stringToMessageData(x_123);
lean_dec(x_123);
x_125 = lean_mk_string_unchecked("", 0, 0);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = l_Lean_MessageData_ofExpr(x_75);
lean_inc(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_mk_string_unchecked(" : ", 3, 3);
x_130 = l_Lean_stringToMessageData(x_129);
lean_dec(x_129);
lean_inc(x_130);
lean_ctor_set_tag(x_72, 7);
lean_ctor_set(x_72, 1, x_130);
lean_ctor_set(x_72, 0, x_128);
x_131 = l_Lean_MessageData_ofExpr(x_118);
if (lean_is_scalar(x_60)) {
 x_132 = lean_alloc_ctor(7, 2, 0);
} else {
 x_132 = x_60;
 lean_ctor_set_tag(x_132, 7);
}
lean_ctor_set(x_132, 0, x_72);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_126);
if (lean_is_scalar(x_57)) {
 x_133 = lean_alloc_ctor(7, 2, 0);
} else {
 x_133 = x_57;
 lean_ctor_set_tag(x_133, 7);
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_126);
x_134 = l_Lean_indentD(x_133);
if (lean_is_scalar(x_55)) {
 x_135 = lean_alloc_ctor(7, 2, 0);
} else {
 x_135 = x_55;
 lean_ctor_set_tag(x_135, 7);
}
lean_ctor_set(x_135, 0, x_124);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_mk_string_unchecked("\nbut is expected to be", 22, 22);
x_137 = l_Lean_stringToMessageData(x_136);
lean_dec(x_136);
if (lean_is_scalar(x_46)) {
 x_138 = lean_alloc_ctor(7, 2, 0);
} else {
 x_138 = x_46;
 lean_ctor_set_tag(x_138, 7);
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_MessageData_ofExpr(x_76);
lean_inc(x_126);
if (lean_is_scalar(x_43)) {
 x_140 = lean_alloc_ctor(7, 2, 0);
} else {
 x_140 = x_43;
 lean_ctor_set_tag(x_140, 7);
}
lean_ctor_set(x_140, 0, x_126);
lean_ctor_set(x_140, 1, x_139);
if (lean_is_scalar(x_41)) {
 x_141 = lean_alloc_ctor(7, 2, 0);
} else {
 x_141 = x_41;
 lean_ctor_set_tag(x_141, 7);
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_130);
x_142 = l_Lean_MessageData_ofExpr(x_119);
if (lean_is_scalar(x_26)) {
 x_143 = lean_alloc_ctor(7, 2, 0);
} else {
 x_143 = x_26;
 lean_ctor_set_tag(x_143, 7);
}
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_inc(x_126);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_126);
x_145 = l_Lean_indentD(x_144);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_138);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_126);
lean_inc(x_64);
x_148 = l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(x_122, x_147, x_62, x_63, x_64, x_65, x_85);
lean_dec(x_122);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_9 = x_62;
x_10 = x_63;
x_11 = x_64;
x_12 = x_65;
x_13 = x_149;
goto block_19;
}
}
else
{
uint8_t x_150; 
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
x_150 = !lean_is_exclusive(x_83);
if (x_150 == 0)
{
return x_83;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_83, 0);
x_152 = lean_ctor_get(x_83, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_83);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_78);
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
x_154 = !lean_is_exclusive(x_80);
if (x_154 == 0)
{
return x_80;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_80, 0);
x_156 = lean_ctor_get(x_80, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_80);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
x_158 = !lean_is_exclusive(x_77);
if (x_158 == 0)
{
return x_77;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_77, 0);
x_160 = lean_ctor_get(x_77, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_77);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_72, 0);
x_163 = lean_ctor_get(x_72, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_72);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_162);
x_164 = lean_infer_type(x_162, x_62, x_63, x_64, x_65, x_73);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_163);
x_167 = lean_infer_type(x_163, x_62, x_63, x_64, x_65, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
x_170 = l_Lean_Meta_addPPExplicitToExposeDiff(x_165, x_168, x_62, x_63, x_64, x_65, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_175 = x_171;
} else {
 lean_dec_ref(x_171);
 x_175 = lean_box(0);
}
x_176 = l_Lean_Elab_Term_instInhabitedCalcStepView;
x_177 = l_Array_back_x21(lean_box(0), x_176, x_1);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_mk_string_unchecked("invalid 'calc' step, right-hand side is", 39, 39);
x_180 = l_Lean_stringToMessageData(x_179);
lean_dec(x_179);
x_181 = lean_mk_string_unchecked("", 0, 0);
x_182 = l_Lean_stringToMessageData(x_181);
lean_dec(x_181);
x_183 = l_Lean_MessageData_ofExpr(x_162);
lean_inc(x_182);
if (lean_is_scalar(x_175)) {
 x_184 = lean_alloc_ctor(7, 2, 0);
} else {
 x_184 = x_175;
 lean_ctor_set_tag(x_184, 7);
}
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_mk_string_unchecked(" : ", 3, 3);
x_186 = l_Lean_stringToMessageData(x_185);
lean_dec(x_185);
lean_inc(x_186);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_MessageData_ofExpr(x_173);
if (lean_is_scalar(x_60)) {
 x_189 = lean_alloc_ctor(7, 2, 0);
} else {
 x_189 = x_60;
 lean_ctor_set_tag(x_189, 7);
}
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_182);
if (lean_is_scalar(x_57)) {
 x_190 = lean_alloc_ctor(7, 2, 0);
} else {
 x_190 = x_57;
 lean_ctor_set_tag(x_190, 7);
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_182);
x_191 = l_Lean_indentD(x_190);
if (lean_is_scalar(x_55)) {
 x_192 = lean_alloc_ctor(7, 2, 0);
} else {
 x_192 = x_55;
 lean_ctor_set_tag(x_192, 7);
}
lean_ctor_set(x_192, 0, x_180);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_mk_string_unchecked("\nbut is expected to be", 22, 22);
x_194 = l_Lean_stringToMessageData(x_193);
lean_dec(x_193);
if (lean_is_scalar(x_46)) {
 x_195 = lean_alloc_ctor(7, 2, 0);
} else {
 x_195 = x_46;
 lean_ctor_set_tag(x_195, 7);
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_MessageData_ofExpr(x_163);
lean_inc(x_182);
if (lean_is_scalar(x_43)) {
 x_197 = lean_alloc_ctor(7, 2, 0);
} else {
 x_197 = x_43;
 lean_ctor_set_tag(x_197, 7);
}
lean_ctor_set(x_197, 0, x_182);
lean_ctor_set(x_197, 1, x_196);
if (lean_is_scalar(x_41)) {
 x_198 = lean_alloc_ctor(7, 2, 0);
} else {
 x_198 = x_41;
 lean_ctor_set_tag(x_198, 7);
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_186);
x_199 = l_Lean_MessageData_ofExpr(x_174);
if (lean_is_scalar(x_26)) {
 x_200 = lean_alloc_ctor(7, 2, 0);
} else {
 x_200 = x_26;
 lean_ctor_set_tag(x_200, 7);
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_inc(x_182);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_182);
x_202 = l_Lean_indentD(x_201);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_195);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_182);
lean_inc(x_64);
x_205 = l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(x_178, x_204, x_62, x_63, x_64, x_65, x_172);
lean_dec(x_178);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_9 = x_62;
x_10 = x_63;
x_11 = x_64;
x_12 = x_65;
x_13 = x_206;
goto block_19;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
x_207 = lean_ctor_get(x_170, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_170, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_209 = x_170;
} else {
 lean_dec_ref(x_170);
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
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
x_211 = lean_ctor_get(x_167, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_167, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_213 = x_167;
} else {
 lean_dec_ref(x_167);
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
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
x_215 = lean_ctor_get(x_164, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_164, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_217 = x_164;
} else {
 lean_dec_ref(x_164);
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
else
{
uint8_t x_219; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
x_219 = !lean_is_exclusive(x_71);
if (x_219 == 0)
{
return x_71;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_71, 0);
x_221 = lean_ctor_get(x_71, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_71);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_26);
if (x_61 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_67, 1);
lean_inc(x_223);
lean_dec(x_67);
x_224 = lean_box(0);
x_225 = l_Lean_Elab_Term_throwCalcFailure___redArg___lam__0(x_2, x_27, x_3, x_224, x_62, x_63, x_64, x_65, x_223);
return x_225;
}
else
{
lean_object* x_226; 
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
x_226 = lean_ctor_get(x_67, 1);
lean_inc(x_226);
lean_dec(x_67);
x_9 = x_62;
x_10 = x_63;
x_11 = x_64;
x_12 = x_65;
x_13 = x_226;
goto block_19;
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_227 = !lean_is_exclusive(x_67);
if (x_227 == 0)
{
return x_67;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_67, 0);
x_229 = lean_ctor_get(x_67, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_67);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
}
}
}
else
{
uint8_t x_412; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_412 = !lean_is_exclusive(x_20);
if (x_412 == 0)
{
return x_20;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_20, 0);
x_414 = lean_ctor_get(x_20, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_20);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
block_19:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_14 = l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0___redArg(x_13);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_throwCalcFailure___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwCalcFailure_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logErrorAt___at___Lean_Elab_Term_throwCalcFailure_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_throwCalcFailure___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_throwCalcFailure___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_throwCalcFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_throwCalcFailure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_throwCalcFailure___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_throwCalcFailure___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("calc", 4, 4);
lean_inc(x_10);
x_12 = l_Lean_Name_mkStr2(x_10, x_11);
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_mk_string_unchecked("calcSteps", 9, 9);
x_18 = l_Lean_Name_mkStr2(x_10, x_17);
lean_inc(x_16);
x_19 = l_Lean_Syntax_isOfKind(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__4___redArg(x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = lean_ctor_get(x_7, 5);
x_24 = l_Lean_replaceRef(x_22, x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 2);
x_28 = lean_ctor_get(x_7, 3);
x_29 = lean_ctor_get(x_7, 4);
x_30 = lean_ctor_get(x_7, 6);
x_31 = lean_ctor_get(x_7, 7);
x_32 = lean_ctor_get(x_7, 8);
x_33 = lean_ctor_get(x_7, 9);
x_34 = lean_ctor_get(x_7, 10);
x_35 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_36 = lean_ctor_get(x_7, 11);
x_37 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_38 = lean_ctor_get(x_7, 12);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_39 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_28);
lean_ctor_set(x_39, 4, x_29);
lean_ctor_set(x_39, 5, x_24);
lean_ctor_set(x_39, 6, x_30);
lean_ctor_set(x_39, 7, x_31);
lean_ctor_set(x_39, 8, x_32);
lean_ctor_set(x_39, 9, x_33);
lean_ctor_set(x_39, 10, x_34);
lean_ctor_set(x_39, 11, x_36);
lean_ctor_set(x_39, 12, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*13, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*13 + 1, x_37);
lean_inc(x_39);
x_40 = l_Lean_Elab_Term_mkCalcStepViews(x_16, x_3, x_4, x_5, x_6, x_39, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_43 = l_Lean_Elab_Term_elabCalcSteps(x_41, x_3, x_4, x_5, x_6, x_39, x_8, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_41);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__0___boxed), 9, 1);
lean_closure_set(x_47, 0, x_41);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___lam__1___boxed), 9, 1);
lean_closure_set(x_48, 0, x_41);
x_49 = l_Lean_Elab_Term_ensureHasTypeWithErrorMsgs(x_2, x_46, x_47, x_48, x_3, x_4, x_5, x_6, x_39, x_8, x_45);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_40);
if (x_54 == 0)
{
return x_40;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_40, 0);
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_40);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCalc___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCalc___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabCalc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabCalc(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("calc", 4, 4);
lean_inc(x_3);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("Elab", 4, 4);
x_7 = lean_mk_string_unchecked("Term", 4, 4);
x_8 = lean_mk_string_unchecked("elabCalc", 8, 8);
x_9 = l_Lean_Name_mkStr4(x_3, x_6, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabCalc___boxed), 9, 0);
x_11 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_5, x_9, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabCalc", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elaborator for the `calc` term mode variant. ", 45, 45);
x_8 = l_Lean_addBuiltinDocString(x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("elabCalc", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(116u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(121u);
x_11 = lean_unsigned_to_nat(15u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(12u);
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
lean_object* initialize_Lean_Elab_App(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Calc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_App(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_instInhabitedCalcStepView = _init_l_Lean_Elab_Term_instInhabitedCalcStepView();
lean_mark_persistent(l_Lean_Elab_Term_instInhabitedCalcStepView);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCalc__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCalc_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Term_elabCalc_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
