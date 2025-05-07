// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Propagate
// Imports: Init.Grind Lean.Meta.Tactic.Grind.Proof Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Ext Lean.Meta.Tactic.Grind.Internalize
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
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_383_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getBoolFalseExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1486_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5969_(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_3906_(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4695_(lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqBoolFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6645_(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_Grind_getFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getExtTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqBoolTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqBoolFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5149_(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_markCaseSplitAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCutsatDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getBoolTrueExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6866_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7247_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1206_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5689_(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqBoolFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at_____private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_985_(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_604_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_2729_(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4184_(lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_8028_(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7748_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7468_(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqBoolTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4439_(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqBoolTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6264_(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_propagateCommRingDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateEqDown_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_3463_(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1766_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = lean_mk_string_unchecked("And", 3, 3);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Expr_isConstOf(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_23);
x_24 = l_Lean_Meta_Grind_isEqTrue___redArg(x_23, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
lean_inc(x_28);
x_29 = l_Lean_Meta_Grind_isEqTrue___redArg(x_28, x_2, x_5, x_8, x_9, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_23);
x_33 = l_Lean_Meta_Grind_isEqFalse(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_28);
x_37 = l_Lean_Meta_Grind_isEqFalse(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
x_47 = l_Lean_Meta_Grind_mkEqFalseProof(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_mk_string_unchecked("Grind", 5, 5);
x_52 = lean_mk_string_unchecked("and_eq_of_eq_false_right", 24, 24);
x_53 = l_Lean_Name_mkStr3(x_50, x_51, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_Expr_const___override(x_53, x_54);
x_56 = l_Lean_mkApp3(x_55, x_23, x_28, x_48);
x_57 = l_Lean_Meta_Grind_pushEqFalse(x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
return x_37;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_37, 0);
x_64 = lean_ctor_get(x_37, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_37);
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
x_66 = lean_ctor_get(x_33, 1);
lean_inc(x_66);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_23);
x_67 = l_Lean_Meta_Grind_mkEqFalseProof(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_mk_string_unchecked("Lean", 4, 4);
x_71 = lean_mk_string_unchecked("Grind", 5, 5);
x_72 = lean_mk_string_unchecked("and_eq_of_eq_false_left", 23, 23);
x_73 = l_Lean_Name_mkStr3(x_70, x_71, x_72);
x_74 = lean_box(0);
x_75 = l_Lean_Expr_const___override(x_73, x_74);
x_76 = l_Lean_mkApp3(x_75, x_23, x_28, x_68);
x_77 = l_Lean_Meta_Grind_pushEqFalse(x_1, x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_67);
if (x_78 == 0)
{
return x_67;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_67, 0);
x_80 = lean_ctor_get(x_67, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_67);
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
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_33);
if (x_82 == 0)
{
return x_33;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_33, 0);
x_84 = lean_ctor_get(x_33, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_33);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_29, 1);
lean_inc(x_86);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
x_87 = l_Lean_Meta_Grind_mkEqTrueProof(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_mk_string_unchecked("Lean", 4, 4);
x_91 = lean_mk_string_unchecked("Grind", 5, 5);
x_92 = lean_mk_string_unchecked("and_eq_of_eq_true_right", 23, 23);
x_93 = l_Lean_Name_mkStr3(x_90, x_91, x_92);
x_94 = lean_box(0);
x_95 = l_Lean_Expr_const___override(x_93, x_94);
lean_inc(x_23);
x_96 = l_Lean_mkApp3(x_95, x_23, x_28, x_88);
x_97 = lean_unbox(x_25);
lean_dec(x_25);
x_98 = l_Lean_Meta_Grind_pushEqCore(x_1, x_23, x_96, x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
return x_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_87, 0);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_29);
if (x_103 == 0)
{
return x_29;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_29, 0);
x_105 = lean_ctor_get(x_29, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_29);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_25);
x_107 = lean_ctor_get(x_24, 1);
lean_inc(x_107);
lean_dec(x_24);
x_108 = lean_ctor_get(x_15, 1);
lean_inc(x_108);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_23);
x_109 = l_Lean_Meta_Grind_mkEqTrueProof(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_mk_string_unchecked("Lean", 4, 4);
x_113 = lean_mk_string_unchecked("Grind", 5, 5);
x_114 = lean_mk_string_unchecked("and_eq_of_eq_true_left", 22, 22);
x_115 = l_Lean_Name_mkStr3(x_112, x_113, x_114);
x_116 = lean_box(0);
x_117 = l_Lean_Expr_const___override(x_115, x_116);
lean_inc(x_108);
x_118 = l_Lean_mkApp3(x_117, x_23, x_108, x_110);
x_119 = lean_box(0);
x_120 = lean_unbox(x_119);
x_121 = l_Lean_Meta_Grind_pushEqCore(x_1, x_108, x_118, x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_111);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_121;
}
else
{
uint8_t x_122; 
lean_dec(x_108);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_109);
if (x_122 == 0)
{
return x_109;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_109, 0);
x_124 = lean_ctor_get(x_109, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_109);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_24);
if (x_126 == 0)
{
return x_24;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_24, 0);
x_128 = lean_ctor_get(x_24, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_24);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_383_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("And", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndUp), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateAndDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = lean_mk_string_unchecked("And", 3, 3);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = l_Lean_Expr_isConstOf(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
if (x_32 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_33; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_mk_string_unchecked("Lean", 4, 4);
x_39 = lean_mk_string_unchecked("Grind", 5, 5);
x_40 = lean_mk_string_unchecked("eq_true_of_and_eq_true_left", 27, 27);
lean_inc(x_39);
lean_inc(x_38);
x_41 = l_Lean_Name_mkStr3(x_38, x_39, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_const___override(x_41, x_42);
lean_inc(x_34);
lean_inc(x_36);
lean_inc(x_37);
x_44 = l_Lean_mkApp3(x_43, x_37, x_36, x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_37);
x_45 = l_Lean_Meta_Grind_pushEqTrue(x_37, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_mk_string_unchecked("eq_true_of_and_eq_true_right", 28, 28);
x_48 = l_Lean_Name_mkStr3(x_38, x_39, x_47);
x_49 = l_Lean_Expr_const___override(x_48, x_42);
lean_inc(x_36);
x_50 = l_Lean_mkApp3(x_49, x_37, x_36, x_34);
x_51 = l_Lean_Meta_Grind_pushEqTrue(x_36, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
}
}
else
{
uint8_t x_52; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_33);
if (x_52 == 0)
{
return x_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_33, 0);
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_33);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
return x_15;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_15, 0);
x_58 = lean_ctor_get(x_15, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_15);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_604_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("And", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateAndDown), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = lean_mk_string_unchecked("Or", 2, 2);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Expr_isConstOf(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_23);
x_24 = l_Lean_Meta_Grind_isEqFalse(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
lean_inc(x_28);
x_29 = l_Lean_Meta_Grind_isEqFalse(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_23);
x_33 = l_Lean_Meta_Grind_isEqTrue___redArg(x_23, x_2, x_5, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_28);
x_37 = l_Lean_Meta_Grind_isEqTrue___redArg(x_28, x_2, x_5, x_8, x_9, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
x_47 = l_Lean_Meta_Grind_mkEqTrueProof(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_mk_string_unchecked("Grind", 5, 5);
x_52 = lean_mk_string_unchecked("or_eq_of_eq_true_right", 22, 22);
x_53 = l_Lean_Name_mkStr3(x_50, x_51, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_Expr_const___override(x_53, x_54);
x_56 = l_Lean_mkApp3(x_55, x_23, x_28, x_48);
x_57 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
return x_37;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_37, 0);
x_64 = lean_ctor_get(x_37, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_37);
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
x_66 = lean_ctor_get(x_33, 1);
lean_inc(x_66);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_23);
x_67 = l_Lean_Meta_Grind_mkEqTrueProof(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_mk_string_unchecked("Lean", 4, 4);
x_71 = lean_mk_string_unchecked("Grind", 5, 5);
x_72 = lean_mk_string_unchecked("or_eq_of_eq_true_left", 21, 21);
x_73 = l_Lean_Name_mkStr3(x_70, x_71, x_72);
x_74 = lean_box(0);
x_75 = l_Lean_Expr_const___override(x_73, x_74);
x_76 = l_Lean_mkApp3(x_75, x_23, x_28, x_68);
x_77 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_67);
if (x_78 == 0)
{
return x_67;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_67, 0);
x_80 = lean_ctor_get(x_67, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_67);
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
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_33);
if (x_82 == 0)
{
return x_33;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_33, 0);
x_84 = lean_ctor_get(x_33, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_33);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_29, 1);
lean_inc(x_86);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
x_87 = l_Lean_Meta_Grind_mkEqFalseProof(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_mk_string_unchecked("Lean", 4, 4);
x_91 = lean_mk_string_unchecked("Grind", 5, 5);
x_92 = lean_mk_string_unchecked("or_eq_of_eq_false_right", 23, 23);
x_93 = l_Lean_Name_mkStr3(x_90, x_91, x_92);
x_94 = lean_box(0);
x_95 = l_Lean_Expr_const___override(x_93, x_94);
lean_inc(x_23);
x_96 = l_Lean_mkApp3(x_95, x_23, x_28, x_88);
x_97 = lean_unbox(x_25);
lean_dec(x_25);
x_98 = l_Lean_Meta_Grind_pushEqCore(x_1, x_23, x_96, x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
return x_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_87, 0);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_29);
if (x_103 == 0)
{
return x_29;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_29, 0);
x_105 = lean_ctor_get(x_29, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_29);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_25);
x_107 = lean_ctor_get(x_24, 1);
lean_inc(x_107);
lean_dec(x_24);
x_108 = lean_ctor_get(x_15, 1);
lean_inc(x_108);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_23);
x_109 = l_Lean_Meta_Grind_mkEqFalseProof(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_mk_string_unchecked("Lean", 4, 4);
x_113 = lean_mk_string_unchecked("Grind", 5, 5);
x_114 = lean_mk_string_unchecked("or_eq_of_eq_false_left", 22, 22);
x_115 = l_Lean_Name_mkStr3(x_112, x_113, x_114);
x_116 = lean_box(0);
x_117 = l_Lean_Expr_const___override(x_115, x_116);
lean_inc(x_108);
x_118 = l_Lean_mkApp3(x_117, x_23, x_108, x_110);
x_119 = lean_box(0);
x_120 = lean_unbox(x_119);
x_121 = l_Lean_Meta_Grind_pushEqCore(x_1, x_108, x_118, x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_111);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_121;
}
else
{
uint8_t x_122; 
lean_dec(x_108);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_109);
if (x_122 == 0)
{
return x_109;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_109, 0);
x_124 = lean_ctor_get(x_109, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_109);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_24);
if (x_126 == 0)
{
return x_24;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_24, 0);
x_128 = lean_ctor_get(x_24, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_24);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_985_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Or", 2, 2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrUp), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateOrDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_isEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = lean_mk_string_unchecked("Or", 2, 2);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = l_Lean_Expr_isConstOf(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
if (x_32 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_33; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_mk_string_unchecked("Lean", 4, 4);
x_39 = lean_mk_string_unchecked("Grind", 5, 5);
x_40 = lean_mk_string_unchecked("eq_false_of_or_eq_false_left", 28, 28);
lean_inc(x_39);
lean_inc(x_38);
x_41 = l_Lean_Name_mkStr3(x_38, x_39, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_const___override(x_41, x_42);
lean_inc(x_34);
lean_inc(x_36);
lean_inc(x_37);
x_44 = l_Lean_mkApp3(x_43, x_37, x_36, x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_37);
x_45 = l_Lean_Meta_Grind_pushEqFalse(x_37, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_mk_string_unchecked("eq_false_of_or_eq_false_right", 29, 29);
x_48 = l_Lean_Name_mkStr3(x_38, x_39, x_47);
x_49 = l_Lean_Expr_const___override(x_48, x_42);
lean_inc(x_36);
x_50 = l_Lean_mkApp3(x_49, x_37, x_36, x_34);
x_51 = l_Lean_Meta_Grind_pushEqFalse(x_36, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
}
}
else
{
uint8_t x_52; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_33);
if (x_52 == 0)
{
return x_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_33, 0);
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_33);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_15);
if (x_56 == 0)
{
return x_15;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_15, 0);
x_58 = lean_ctor_get(x_15, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_15);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1206_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Or", 2, 2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateOrDown), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = lean_mk_string_unchecked("Not", 3, 3);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Expr_isConstOf(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
lean_inc(x_21);
x_22 = l_Lean_Meta_Grind_isEqFalse(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_21);
x_26 = l_Lean_Meta_Grind_isEqTrue___redArg(x_21, x_2, x_5, x_8, x_9, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_21, x_2, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_21);
x_40 = lean_grind_mk_eq_proof(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_mk_string_unchecked("Lean", 4, 4);
x_44 = lean_mk_string_unchecked("Grind", 5, 5);
x_45 = lean_mk_string_unchecked("false_of_not_eq_self", 20, 20);
x_46 = l_Lean_Name_mkStr3(x_43, x_44, x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Expr_const___override(x_46, x_47);
x_49 = l_Lean_mkAppB(x_48, x_21, x_41);
x_50 = l_Lean_Meta_Grind_closeGoal(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_21);
x_56 = l_Lean_Meta_Grind_mkEqTrueProof(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_mk_string_unchecked("Lean", 4, 4);
x_60 = lean_mk_string_unchecked("Grind", 5, 5);
x_61 = lean_mk_string_unchecked("not_eq_of_eq_true", 17, 17);
x_62 = l_Lean_Name_mkStr3(x_59, x_60, x_61);
x_63 = lean_box(0);
x_64 = l_Lean_Expr_const___override(x_62, x_63);
x_65 = l_Lean_mkAppB(x_64, x_21, x_57);
x_66 = l_Lean_Meta_Grind_pushEqFalse(x_1, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_56);
if (x_67 == 0)
{
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_56, 0);
x_69 = lean_ctor_get(x_56, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_56);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_26);
if (x_71 == 0)
{
return x_26;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_26, 0);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_26);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_22, 1);
lean_inc(x_75);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_21);
x_76 = l_Lean_Meta_Grind_mkEqFalseProof(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_mk_string_unchecked("Lean", 4, 4);
x_80 = lean_mk_string_unchecked("Grind", 5, 5);
x_81 = lean_mk_string_unchecked("not_eq_of_eq_false", 18, 18);
x_82 = l_Lean_Name_mkStr3(x_79, x_80, x_81);
x_83 = lean_box(0);
x_84 = l_Lean_Expr_const___override(x_82, x_83);
x_85 = l_Lean_mkAppB(x_84, x_21, x_77);
x_86 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_76);
if (x_87 == 0)
{
return x_76;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_76, 0);
x_89 = lean_ctor_get(x_76, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_76);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_22);
if (x_91 == 0)
{
return x_22;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_22, 0);
x_93 = lean_ctor_get(x_22, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_22);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1486_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Not", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotUp), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNotDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = lean_mk_string_unchecked("Not", 3, 3);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Expr_isConstOf(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; 
lean_inc(x_1);
x_21 = l_Lean_Meta_Grind_isEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
lean_inc(x_1);
x_26 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_25, x_2, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_25);
x_40 = lean_grind_mk_eq_proof(x_1, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_mk_string_unchecked("Lean", 4, 4);
x_44 = lean_mk_string_unchecked("Grind", 5, 5);
x_45 = lean_mk_string_unchecked("false_of_not_eq_self", 20, 20);
x_46 = l_Lean_Name_mkStr3(x_43, x_44, x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Expr_const___override(x_46, x_47);
x_49 = l_Lean_mkAppB(x_48, x_25, x_41);
x_50 = l_Lean_Meta_Grind_closeGoal(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_56 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_mk_string_unchecked("Lean", 4, 4);
x_60 = lean_mk_string_unchecked("Grind", 5, 5);
x_61 = lean_mk_string_unchecked("eq_false_of_not_eq_true", 23, 23);
x_62 = l_Lean_Name_mkStr3(x_59, x_60, x_61);
x_63 = lean_box(0);
x_64 = l_Lean_Expr_const___override(x_62, x_63);
lean_inc(x_25);
x_65 = l_Lean_mkAppB(x_64, x_25, x_57);
x_66 = l_Lean_Meta_Grind_pushEqFalse(x_25, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_56);
if (x_67 == 0)
{
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_56, 0);
x_69 = lean_ctor_get(x_56, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_56);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_26);
if (x_71 == 0)
{
return x_26;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_26, 0);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_26);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_dec(x_21);
x_76 = lean_ctor_get(x_15, 1);
lean_inc(x_76);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_77 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_mk_string_unchecked("Lean", 4, 4);
x_81 = lean_mk_string_unchecked("Grind", 5, 5);
x_82 = lean_mk_string_unchecked("eq_true_of_not_eq_false", 23, 23);
x_83 = l_Lean_Name_mkStr3(x_80, x_81, x_82);
x_84 = lean_box(0);
x_85 = l_Lean_Expr_const___override(x_83, x_84);
lean_inc(x_76);
x_86 = l_Lean_mkAppB(x_85, x_76, x_78);
x_87 = l_Lean_Meta_Grind_pushEqTrue(x_76, x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_79);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_76);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_77);
if (x_88 == 0)
{
return x_77;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_77, 0);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_77);
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
uint8_t x_92; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_21);
if (x_92 == 0)
{
return x_21;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_21, 0);
x_94 = lean_ctor_get(x_21, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_21);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1766_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Not", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNotDown), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Lean_Meta_Grind_getBoolFalseExpr___redArg(x_5, x_10);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Lean_Meta_Grind_mkDiseqProof_x3f(x_1, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_52;
goto block_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_mk_string_unchecked("Lean", 4, 4);
x_56 = lean_mk_string_unchecked("Grind", 5, 5);
x_57 = lean_mk_string_unchecked("Bool", 4, 4);
x_58 = lean_mk_string_unchecked("eq_true_of_not_eq_false'", 24, 24);
x_59 = l_Lean_Name_mkStr4(x_55, x_56, x_57, x_58);
x_60 = lean_box(0);
x_61 = l_Lean_Expr_const___override(x_59, x_60);
lean_inc(x_1);
x_62 = l_Lean_mkAppB(x_61, x_1, x_54);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_63 = l_Lean_Meta_Grind_pushEqBoolTrue(x_1, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_64;
goto block_46;
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
lean_dec(x_1);
return x_63;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_50);
if (x_65 == 0)
{
return x_50;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
block_46:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_Meta_Grind_getBoolTrueExpr___redArg(x_14, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_23 = l_Lean_Meta_Grind_mkDiseqProof_x3f(x_1, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_mk_string_unchecked("Lean", 4, 4);
x_34 = lean_mk_string_unchecked("Grind", 5, 5);
x_35 = lean_mk_string_unchecked("Bool", 4, 4);
x_36 = lean_mk_string_unchecked("eq_false_of_not_eq_true'", 24, 24);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_box(0);
x_39 = l_Lean_Expr_const___override(x_37, x_38);
lean_inc(x_1);
x_40 = l_Lean_mkAppB(x_39, x_1, x_32);
x_41 = l_Lean_Meta_Grind_pushEqBoolFalse(x_1, x_40, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = lean_grind_mk_eq_proof(x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
x_20 = l_Lean_Meta_mkEqTrans(x_18, x_7, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = lean_grind_mk_eq_proof(x_3, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_26 = l_Lean_Meta_mkEqTrans(x_21, x_24, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_Grind_getFalseExpr(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_32 = l_Lean_Meta_mkNoConfusion(x_30, x_27, x_12, x_13, x_14, x_15, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_mk_empty_array_with_capacity(x_35);
x_37 = lean_array_push(x_36, x_7);
x_38 = lean_box(1);
x_39 = lean_unbox(x_38);
x_40 = l_Lean_Meta_mkLambdaFVars(x_37, x_33, x_5, x_6, x_5, x_39, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_37);
return x_40;
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
return x_32;
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
lean_dec(x_9);
lean_dec(x_7);
return x_26;
}
}
else
{
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_23;
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_19 = l_Lean_Expr_cleanupAnnotations(x_1);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
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
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
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
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
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
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = lean_mk_string_unchecked("Eq", 2, 2);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = l_Lean_Expr_isConstOf(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
if (x_28 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
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
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_29);
x_30 = l_Lean_Meta_Grind_isEqTrue___redArg(x_29, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_132; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_dec(x_19);
x_105 = lean_ctor_get(x_23, 1);
lean_inc(x_105);
lean_dec(x_23);
x_132 = lean_unbox(x_31);
if (x_132 == 0)
{
lean_object* x_133; 
lean_inc(x_33);
x_133 = l_Lean_Meta_Grind_isEqTrue___redArg(x_33, x_2, x_5, x_8, x_9, x_32);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_31);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = l_Lean_Meta_Grind_isEqv___redArg(x_29, x_33, x_2, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
x_110 = x_6;
x_111 = x_7;
x_112 = x_8;
x_113 = x_9;
x_114 = x_140;
goto block_131;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_33);
lean_inc(x_29);
x_142 = lean_grind_mk_eq_proof(x_29, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_1);
x_145 = l_Lean_Meta_mkEqTrueCore(x_1, x_143);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_146 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
x_110 = x_6;
x_111 = x_7;
x_112 = x_8;
x_113 = x_9;
x_114 = x_147;
goto block_131;
}
else
{
lean_dec(x_105);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_146;
}
}
else
{
uint8_t x_148; 
lean_dec(x_105);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_142);
if (x_148 == 0)
{
return x_142;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_142, 0);
x_150 = lean_ctor_get(x_142, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_142);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_133, 1);
lean_inc(x_152);
lean_dec(x_133);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_33);
x_153 = l_Lean_Meta_Grind_mkEqTrueProof(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_mk_string_unchecked("Lean", 4, 4);
x_157 = lean_mk_string_unchecked("Grind", 5, 5);
x_158 = lean_mk_string_unchecked("eq_eq_of_eq_true_right", 22, 22);
x_159 = l_Lean_Name_mkStr3(x_156, x_157, x_158);
x_160 = lean_box(0);
x_161 = l_Lean_Expr_const___override(x_159, x_160);
lean_inc(x_33);
lean_inc(x_29);
x_162 = l_Lean_mkApp3(x_161, x_29, x_33, x_154);
x_163 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
lean_inc(x_1);
x_164 = l_Lean_Meta_Grind_pushEqCore(x_1, x_29, x_162, x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_155);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
x_110 = x_6;
x_111 = x_7;
x_112 = x_8;
x_113 = x_9;
x_114 = x_165;
goto block_131;
}
else
{
lean_dec(x_105);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_164;
}
}
else
{
uint8_t x_166; 
lean_dec(x_105);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_153);
if (x_166 == 0)
{
return x_153;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_153, 0);
x_168 = lean_ctor_get(x_153, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_153);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_105);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_133);
if (x_170 == 0)
{
return x_133;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_133, 0);
x_172 = lean_ctor_get(x_133, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_133);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_174 = l_Lean_Meta_Grind_mkEqTrueProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_mk_string_unchecked("Lean", 4, 4);
x_178 = lean_mk_string_unchecked("Grind", 5, 5);
x_179 = lean_mk_string_unchecked("eq_eq_of_eq_true_left", 21, 21);
x_180 = l_Lean_Name_mkStr3(x_177, x_178, x_179);
x_181 = lean_box(0);
x_182 = l_Lean_Expr_const___override(x_180, x_181);
lean_inc(x_33);
lean_inc(x_29);
x_183 = l_Lean_mkApp3(x_182, x_29, x_33, x_175);
x_184 = lean_box(0);
x_185 = lean_unbox(x_184);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
lean_inc(x_1);
x_186 = l_Lean_Meta_Grind_pushEqCore(x_1, x_33, x_183, x_185, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_176);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_106 = x_2;
x_107 = x_3;
x_108 = x_4;
x_109 = x_5;
x_110 = x_6;
x_111 = x_7;
x_112 = x_8;
x_113 = x_9;
x_114 = x_187;
goto block_131;
}
else
{
lean_dec(x_105);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_186;
}
}
else
{
uint8_t x_188; 
lean_dec(x_105);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_174);
if (x_188 == 0)
{
return x_174;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_174, 0);
x_190 = lean_ctor_get(x_174, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_174);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
block_76:
{
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_1);
x_15 = x_41;
goto block_18;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec(x_34);
x_47 = l_Lean_Expr_getAppFn(x_46);
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
lean_dec(x_36);
x_49 = l_Lean_Expr_getAppFn(x_48);
x_50 = lean_expr_eqv(x_47, x_49);
lean_dec(x_49);
lean_dec(x_47);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_42);
lean_inc(x_39);
lean_inc(x_43);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_29);
x_51 = l_Lean_Meta_mkEq(x_29, x_33, x_35, x_43, x_39, x_42, x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(x_50);
x_55 = lean_box(x_28);
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed), 16, 6);
lean_closure_set(x_56, 0, x_46);
lean_closure_set(x_56, 1, x_29);
lean_closure_set(x_56, 2, x_33);
lean_closure_set(x_56, 3, x_48);
lean_closure_set(x_56, 4, x_54);
lean_closure_set(x_56, 5, x_55);
x_57 = lean_mk_string_unchecked("h", 1, 1);
x_58 = l_Lean_Name_mkStr1(x_57);
lean_inc(x_42);
lean_inc(x_39);
lean_inc(x_43);
lean_inc(x_35);
lean_inc(x_40);
lean_inc(x_37);
lean_inc(x_38);
lean_inc(x_44);
x_59 = l_Lean_Meta_withLocalDeclD___at_____private_Lean_Meta_Tactic_Grind_Proof_0__Lean_Meta_Grind_mkHCongrProof_spec__0(lean_box(0), x_58, x_52, x_56, x_44, x_38, x_37, x_40, x_35, x_43, x_39, x_42, x_53);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_mk_string_unchecked("eq_false", 8, 8);
x_63 = l_Lean_Name_mkStr1(x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Expr_const___override(x_63, x_64);
lean_inc(x_1);
x_66 = l_Lean_mkAppB(x_65, x_1, x_60);
x_67 = l_Lean_Meta_Grind_pushEqFalse(x_1, x_66, x_44, x_38, x_37, x_40, x_35, x_43, x_39, x_42, x_61);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_38);
lean_dec(x_44);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_59);
if (x_68 == 0)
{
return x_59;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_59, 0);
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_59);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_51);
if (x_72 == 0)
{
return x_51;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_51, 0);
x_74 = lean_ctor_get(x_51, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_51);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_1);
x_15 = x_41;
goto block_18;
}
}
}
block_104:
{
lean_object* x_86; 
lean_inc(x_29);
x_86 = l_Lean_Meta_Grind_getRootENode___redArg(x_29, x_77, x_83, x_84, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_33);
x_89 = l_Lean_Meta_Grind_getRootENode___redArg(x_33, x_77, x_83, x_84, x_88);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_87, sizeof(void*)*13 + 2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_34 = x_87;
x_35 = x_81;
x_36 = x_91;
x_37 = x_79;
x_38 = x_78;
x_39 = x_83;
x_40 = x_80;
x_41 = x_92;
x_42 = x_84;
x_43 = x_82;
x_44 = x_77;
x_45 = x_90;
goto block_76;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_ctor_get_uint8(x_93, sizeof(void*)*13 + 2);
x_34 = x_87;
x_35 = x_81;
x_36 = x_93;
x_37 = x_79;
x_38 = x_78;
x_39 = x_83;
x_40 = x_80;
x_41 = x_94;
x_42 = x_84;
x_43 = x_82;
x_44 = x_77;
x_45 = x_95;
goto block_76;
}
}
else
{
uint8_t x_96; 
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_89);
if (x_96 == 0)
{
return x_89;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_89, 0);
x_98 = lean_ctor_get(x_89, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_89);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_86);
if (x_100 == 0)
{
return x_86;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_86, 0);
x_102 = lean_ctor_get(x_86, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_86);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_131:
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_mk_string_unchecked("Bool", 4, 4);
x_116 = l_Lean_Name_mkStr1(x_115);
x_117 = l_Lean_Expr_isConstOf(x_105, x_116);
lean_dec(x_116);
lean_dec(x_105);
if (x_117 == 0)
{
x_77 = x_106;
x_78 = x_107;
x_79 = x_108;
x_80 = x_109;
x_81 = x_110;
x_82 = x_111;
x_83 = x_112;
x_84 = x_113;
x_85 = x_114;
goto block_104;
}
else
{
lean_object* x_118; 
lean_inc(x_1);
x_118 = l_Lean_Meta_Grind_isEqFalse(x_1, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_77 = x_106;
x_78 = x_107;
x_79 = x_108;
x_80 = x_109;
x_81 = x_110;
x_82 = x_111;
x_83 = x_112;
x_84 = x_113;
x_85 = x_121;
goto block_104;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_29);
x_123 = l_Lean_Meta_Grind_propagateBoolDiseq(x_29, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_33);
x_125 = l_Lean_Meta_Grind_propagateBoolDiseq(x_33, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_77 = x_106;
x_78 = x_107;
x_79 = x_108;
x_80 = x_109;
x_81 = x_110;
x_82 = x_111;
x_83 = x_112;
x_84 = x_113;
x_85 = x_126;
goto block_104;
}
else
{
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_1);
return x_125;
}
}
else
{
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_1);
return x_123;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_118);
if (x_127 == 0)
{
return x_118;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_118, 0);
x_129 = lean_ctor_get(x_118, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_118);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_29);
lean_dec(x_23);
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
x_192 = !lean_is_exclusive(x_30);
if (x_192 == 0)
{
return x_30;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_30, 0);
x_194 = lean_ctor_get(x_30, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_30);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
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
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqUp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = l_Lean_Meta_Grind_propagateEqUp___lam__0(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_2729_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Eq", 2, 2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqUp), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateEqDown_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_array_uget(x_2, x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_18 = l_Lean_Meta_Grind_instantiateExtTheorem(x_17, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_4, x_22);
x_4 = x_23;
x_5 = x_20;
x_14 = x_19;
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
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; lean_object* x_23; lean_object* x_27; 
lean_inc(x_1);
x_27 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_1);
x_31 = l_Lean_Meta_Grind_isEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
lean_inc(x_1);
x_41 = l_Lean_Expr_cleanupAnnotations(x_1);
x_42 = l_Lean_Expr_isApp(x_41);
if (x_42 == 0)
{
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
x_19 = x_40;
goto block_22;
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_inc(x_41);
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_41);
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_dec(x_43);
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
x_19 = x_40;
goto block_22;
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_inc(x_43);
x_45 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_46 = l_Lean_Expr_isApp(x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_43);
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
x_19 = x_40;
goto block_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_45);
x_47 = l_Lean_Expr_appFnCleanup___redArg(x_45);
x_48 = lean_mk_string_unchecked("Eq", 2, 2);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = l_Lean_Expr_isConstOf(x_47, x_49);
lean_dec(x_49);
lean_dec(x_47);
if (x_50 == 0)
{
lean_dec(x_45);
lean_dec(x_43);
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
x_19 = x_40;
goto block_22;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_dec(x_41);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_122 = lean_mk_string_unchecked("Bool", 4, 4);
x_123 = l_Lean_Name_mkStr1(x_122);
x_124 = l_Lean_Expr_isConstOf(x_53, x_123);
lean_dec(x_123);
if (x_124 == 0)
{
x_81 = x_2;
x_82 = x_3;
x_83 = x_4;
x_84 = x_5;
x_85 = x_6;
x_86 = x_7;
x_87 = x_8;
x_88 = x_9;
x_89 = x_40;
goto block_121;
}
else
{
lean_object* x_125; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_52);
x_125 = l_Lean_Meta_Grind_propagateBoolDiseq(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_51);
x_127 = l_Lean_Meta_Grind_propagateBoolDiseq(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_81 = x_2;
x_82 = x_3;
x_83 = x_4;
x_84 = x_5;
x_85 = x_6;
x_86 = x_7;
x_87 = x_8;
x_88 = x_9;
x_89 = x_128;
goto block_121;
}
else
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
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
else
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_125;
}
}
block_80:
{
if (x_63 == 0)
{
lean_object* x_64; 
lean_inc(x_56);
lean_inc(x_62);
lean_inc(x_59);
x_64 = l_Lean_Meta_Grind_getExtTheorems(x_53, x_54, x_55, x_60, x_58, x_57, x_59, x_62, x_56, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; lean_object* x_69; size_t x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
x_68 = lean_array_size(x_65);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_usize_of_nat(x_69);
x_71 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateEqDown_spec__0(x_1, x_65, x_68, x_70, x_67, x_54, x_55, x_60, x_58, x_57, x_59, x_62, x_56, x_66);
lean_dec(x_65);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_67);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
return x_71;
}
}
else
{
uint8_t x_76; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_64, 0);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_1);
x_15 = x_61;
goto block_18;
}
}
block_121:
{
lean_object* x_90; 
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_51);
lean_inc(x_52);
x_90 = l_Lean_Meta_Grind_propagateCutsatDiseq(x_52, x_51, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_51);
lean_inc(x_52);
x_92 = l_Lean_Meta_Grind_propagateCommRingDiseq(x_52, x_51, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_53);
x_94 = l_Lean_Meta_Grind_getExtTheorems(x_53, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Array_isEmpty___redArg(x_95);
lean_dec(x_95);
if (x_97 == 0)
{
if (x_50 == 0)
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
x_11 = x_96;
goto block_14;
}
else
{
lean_object* x_98; 
x_98 = l_Lean_Meta_Grind_getRootENode___redArg(x_52, x_81, x_87, x_88, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Meta_Grind_getRootENode___redArg(x_51, x_81, x_87, x_88, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_mk_string_unchecked("List", 4, 4);
x_105 = l_Lean_Name_mkStr1(x_104);
x_106 = l_Lean_Expr_isAppOf(x_53, x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_dec(x_102);
lean_dec(x_99);
x_54 = x_81;
x_55 = x_82;
x_56 = x_88;
x_57 = x_85;
x_58 = x_84;
x_59 = x_86;
x_60 = x_83;
x_61 = x_103;
x_62 = x_87;
x_63 = x_106;
goto block_80;
}
else
{
uint8_t x_107; 
x_107 = lean_ctor_get_uint8(x_99, sizeof(void*)*13 + 2);
lean_dec(x_99);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = lean_ctor_get_uint8(x_102, sizeof(void*)*13 + 2);
lean_dec(x_102);
x_54 = x_81;
x_55 = x_82;
x_56 = x_88;
x_57 = x_85;
x_58 = x_84;
x_59 = x_86;
x_60 = x_83;
x_61 = x_103;
x_62 = x_87;
x_63 = x_108;
goto block_80;
}
else
{
lean_dec(x_102);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_53);
lean_dec(x_1);
x_15 = x_103;
goto block_18;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_53);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_101);
if (x_109 == 0)
{
return x_101;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_101, 0);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_101);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_98);
if (x_113 == 0)
{
return x_98;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_98, 0);
x_115 = lean_ctor_get(x_98, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_98);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
x_11 = x_96;
goto block_14;
}
}
else
{
uint8_t x_117; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_94);
if (x_117 == 0)
{
return x_94;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_94, 0);
x_119 = lean_ctor_get(x_94, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_94);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
return x_92;
}
}
else
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
return x_90;
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
uint8_t x_129; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_31);
if (x_129 == 0)
{
return x_31;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_31, 0);
x_131 = lean_ctor_get(x_31, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_31);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_27, 1);
lean_inc(x_133);
lean_dec(x_27);
lean_inc(x_1);
x_134 = l_Lean_Expr_cleanupAnnotations(x_1);
x_135 = l_Lean_Expr_isApp(x_134);
if (x_135 == 0)
{
lean_dec(x_134);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = x_133;
goto block_26;
}
else
{
lean_object* x_136; uint8_t x_137; 
lean_inc(x_134);
x_136 = l_Lean_Expr_appFnCleanup___redArg(x_134);
x_137 = l_Lean_Expr_isApp(x_136);
if (x_137 == 0)
{
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = x_133;
goto block_26;
}
else
{
lean_object* x_138; uint8_t x_139; 
lean_inc(x_136);
x_138 = l_Lean_Expr_appFnCleanup___redArg(x_136);
x_139 = l_Lean_Expr_isApp(x_138);
if (x_139 == 0)
{
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = x_133;
goto block_26;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = l_Lean_Expr_appFnCleanup___redArg(x_138);
x_141 = lean_mk_string_unchecked("Eq", 2, 2);
x_142 = l_Lean_Name_mkStr1(x_141);
x_143 = l_Lean_Expr_isConstOf(x_140, x_142);
lean_dec(x_142);
lean_dec(x_140);
if (x_143 == 0)
{
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = x_133;
goto block_26;
}
else
{
lean_object* x_144; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_144 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_133);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_134, 1);
lean_inc(x_147);
lean_dec(x_134);
x_148 = lean_ctor_get(x_136, 1);
lean_inc(x_148);
lean_dec(x_136);
x_149 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_145);
x_150 = lean_box(0);
x_151 = lean_unbox(x_150);
x_152 = l_Lean_Meta_Grind_pushEqCore(x_148, x_147, x_149, x_151, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_146);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_152;
}
else
{
uint8_t x_153; 
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_144);
if (x_153 == 0)
{
return x_144;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_144, 0);
x_155 = lean_ctor_get(x_144, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_144);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
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
uint8_t x_157; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_27);
if (x_157 == 0)
{
return x_27;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_27, 0);
x_159 = lean_ctor_get(x_27, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_27);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
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
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateEqDown_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_propagateEqDown_spec__0(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_3463_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Eq", 2, 2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqDown), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBEqUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_inc(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = lean_mk_string_unchecked("BEq", 3, 3);
x_25 = lean_mk_string_unchecked("beq", 3, 3);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = l_Lean_Expr_isConstOf(x_23, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = l_Lean_Meta_Grind_isEqv___redArg(x_29, x_28, x_2, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
lean_inc(x_29);
x_36 = l_Lean_Meta_Grind_mkDiseqProof_x3f(x_29, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
x_46 = l_Lean_Expr_constLevels_x21(x_23);
lean_dec(x_23);
x_47 = lean_mk_string_unchecked("LawfulBEq", 9, 9);
x_48 = l_Lean_Name_mkStr1(x_47);
lean_inc(x_46);
x_49 = l_Lean_Expr_const___override(x_48, x_46);
lean_inc(x_34);
lean_inc(x_35);
x_50 = l_Lean_mkAppB(x_49, x_35, x_34);
x_51 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_52 = l_Lean_Meta_trySynthInstance(x_50, x_51, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_mk_string_unchecked("Lean", 4, 4);
x_57 = lean_mk_string_unchecked("Grind", 5, 5);
x_58 = lean_mk_string_unchecked("beq_eq_false_of_diseq", 21, 21);
x_59 = l_Lean_Name_mkStr3(x_56, x_57, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_46);
x_61 = l_Lean_mkApp6(x_60, x_35, x_34, x_55, x_29, x_28, x_45);
x_62 = l_Lean_Meta_Grind_pushEqBoolFalse(x_1, x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_53);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_52, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set(x_52, 0, x_65);
return x_52;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
lean_dec(x_52);
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
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
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
uint8_t x_73; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_36);
if (x_73 == 0)
{
return x_36;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_36, 0);
x_75 = lean_ctor_get(x_36, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_36);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_30, 1);
lean_inc(x_77);
lean_dec(x_30);
x_78 = lean_ctor_get(x_19, 1);
lean_inc(x_78);
lean_dec(x_19);
x_79 = lean_ctor_get(x_21, 1);
lean_inc(x_79);
lean_dec(x_21);
x_80 = l_Lean_Expr_constLevels_x21(x_23);
lean_dec(x_23);
x_81 = lean_mk_string_unchecked("LawfulBEq", 9, 9);
x_82 = l_Lean_Name_mkStr1(x_81);
lean_inc(x_80);
x_83 = l_Lean_Expr_const___override(x_82, x_80);
lean_inc(x_78);
lean_inc(x_79);
x_84 = l_Lean_mkAppB(x_83, x_79, x_78);
x_85 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_86 = l_Lean_Meta_trySynthInstance(x_84, x_85, x_6, x_7, x_8, x_9, x_77);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 1)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
lean_inc(x_29);
x_90 = lean_grind_mk_eq_proof(x_29, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_mk_string_unchecked("Lean", 4, 4);
x_94 = lean_mk_string_unchecked("Grind", 5, 5);
x_95 = lean_mk_string_unchecked("beq_eq_true_of_eq", 17, 17);
x_96 = l_Lean_Name_mkStr3(x_93, x_94, x_95);
x_97 = l_Lean_Expr_const___override(x_96, x_80);
x_98 = l_Lean_mkApp6(x_97, x_79, x_78, x_89, x_29, x_28, x_91);
x_99 = l_Lean_Meta_Grind_pushEqBoolTrue(x_1, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_92);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_89);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_90);
if (x_100 == 0)
{
return x_90;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_90, 0);
x_102 = lean_ctor_get(x_90, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_90);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_87);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_86);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_86, 0);
lean_dec(x_105);
x_106 = lean_box(0);
lean_ctor_set(x_86, 0, x_106);
return x_86;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_86, 1);
lean_inc(x_107);
lean_dec(x_86);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_86);
if (x_110 == 0)
{
return x_86;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_86, 0);
x_112 = lean_ctor_get(x_86, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_86);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_3906_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("BEq", 3, 3);
x_3 = lean_mk_string_unchecked("beq", 3, 3);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBEqUp), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateEqMatchDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_inc(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_inc(x_29);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Grind", 5, 5);
x_36 = lean_mk_string_unchecked("EqMatch", 7, 7);
x_37 = l_Lean_Name_mkStr3(x_34, x_35, x_36);
x_38 = l_Lean_Expr_isConstOf(x_33, x_37);
lean_dec(x_37);
lean_dec(x_33);
if (x_38 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_dec(x_25);
x_40 = l_Lean_Meta_Grind_markCaseSplitAsResolved(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_dec(x_29);
x_47 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_43);
x_48 = lean_box(0);
x_49 = lean_unbox(x_48);
x_50 = l_Lean_Meta_Grind_pushEqCore(x_46, x_45, x_47, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_40;
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
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_15);
if (x_55 == 0)
{
return x_15;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4184_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("EqMatch", 7, 7);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateEqMatchDown), 10, 0);
x_7 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_inc(x_29);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = lean_mk_string_unchecked("HEq", 3, 3);
x_35 = l_Lean_Name_mkStr1(x_34);
x_36 = l_Lean_Expr_isConstOf(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
if (x_36 == 0)
{
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_37; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_37 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_38);
x_43 = l_Lean_Meta_Grind_pushEqCore(x_41, x_40, x_42, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
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
uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4439_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("HEq", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqDown), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateHEqUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = lean_mk_string_unchecked("HEq", 3, 3);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Meta_Grind_isEqv___redArg(x_28, x_27, x_2, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_39 = lean_grind_mk_heq_proof(x_28, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkEqTrueCore(x_1, x_40);
x_43 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4695_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("HEq", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateHEqUp), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = lean_mk_string_unchecked("ite", 3, 3);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = l_Lean_Expr_isConstOf(x_25, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_29);
x_30 = l_Lean_Meta_Grind_isEqTrue___redArg(x_29, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
lean_inc(x_29);
x_38 = l_Lean_Meta_Grind_isEqFalse(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_34);
x_52 = lean_grind_internalize(x_34, x_49, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_54 = l_Lean_Meta_Grind_mkEqFalseProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_mk_string_unchecked("ite_cond_eq_false", 17, 17);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = l_Lean_Expr_constLevels_x21(x_25);
lean_dec(x_25);
x_60 = l_Lean_Expr_const___override(x_58, x_59);
lean_inc(x_34);
x_61 = l_Lean_mkApp6(x_60, x_37, x_29, x_36, x_35, x_34, x_55);
x_62 = lean_unbox(x_31);
lean_dec(x_31);
x_63 = l_Lean_Meta_Grind_pushEqCore(x_1, x_34, x_61, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
return x_54;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_52;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_38);
if (x_68 == 0)
{
return x_38;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_38, 0);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_38);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_31);
x_72 = lean_ctor_get(x_30, 1);
lean_inc(x_72);
lean_dec(x_30);
x_73 = lean_ctor_get(x_15, 1);
lean_inc(x_73);
lean_dec(x_15);
x_74 = lean_ctor_get(x_17, 1);
lean_inc(x_74);
lean_dec(x_17);
x_75 = lean_ctor_get(x_19, 1);
lean_inc(x_75);
lean_dec(x_19);
x_76 = lean_ctor_get(x_23, 1);
lean_inc(x_76);
lean_dec(x_23);
x_77 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_72);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_74);
x_81 = lean_grind_internalize(x_74, x_78, x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_83 = l_Lean_Meta_Grind_mkEqTrueProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_mk_string_unchecked("ite_cond_eq_true", 16, 16);
x_87 = l_Lean_Name_mkStr1(x_86);
x_88 = l_Lean_Expr_constLevels_x21(x_25);
lean_dec(x_25);
x_89 = l_Lean_Expr_const___override(x_87, x_88);
lean_inc(x_74);
x_90 = l_Lean_mkApp6(x_89, x_76, x_29, x_75, x_74, x_73, x_84);
x_91 = lean_box(0);
x_92 = lean_unbox(x_91);
x_93 = l_Lean_Meta_Grind_pushEqCore(x_1, x_74, x_90, x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_83);
if (x_94 == 0)
{
return x_83;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_83, 0);
x_96 = lean_ctor_get(x_83, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_83);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_81;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_30);
if (x_98 == 0)
{
return x_30;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_30, 0);
x_100 = lean_ctor_get(x_30, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_30);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5149_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("ite", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateIte), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = lean_mk_string_unchecked("dite", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = l_Lean_Expr_isConstOf(x_25, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_29);
x_30 = l_Lean_Meta_Grind_isEqTrue___redArg(x_29, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
lean_inc(x_29);
x_38 = l_Lean_Meta_Grind_isEqFalse(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_48 = l_Lean_Meta_Grind_mkEqFalseProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_49);
lean_inc(x_29);
x_51 = l_Lean_Meta_mkOfEqFalseCore(x_29, x_49);
lean_inc(x_34);
x_52 = l_Lean_Expr_app___override(x_34, x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_53 = l_Lean_Meta_Grind_preprocess(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_54);
x_56 = l_Lean_Meta_Simp_Result_getProof(x_54, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_62);
x_64 = lean_grind_internalize(x_62, x_60, x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_mk_string_unchecked("Lean", 4, 4);
x_67 = lean_mk_string_unchecked("Grind", 5, 5);
x_68 = lean_mk_string_unchecked("dite_cond_eq_false'", 19, 19);
x_69 = l_Lean_Name_mkStr3(x_66, x_67, x_68);
x_70 = l_Lean_Expr_constLevels_x21(x_25);
lean_dec(x_25);
x_71 = l_Lean_Expr_const___override(x_69, x_70);
lean_inc(x_62);
x_72 = l_Lean_mkApp8(x_71, x_37, x_29, x_36, x_35, x_34, x_62, x_49, x_57);
x_73 = lean_unbox(x_31);
lean_dec(x_31);
x_74 = l_Lean_Meta_Grind_pushEqCore(x_1, x_62, x_72, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_74;
}
else
{
lean_dec(x_62);
lean_dec(x_57);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_64;
}
}
else
{
uint8_t x_75; 
lean_dec(x_54);
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_56);
if (x_75 == 0)
{
return x_56;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_56, 0);
x_77 = lean_ctor_get(x_56, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_56);
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
lean_dec(x_49);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_53);
if (x_79 == 0)
{
return x_53;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_53, 0);
x_81 = lean_ctor_get(x_53, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_53);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_48);
if (x_83 == 0)
{
return x_48;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_48, 0);
x_85 = lean_ctor_get(x_48, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_48);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_38);
if (x_87 == 0)
{
return x_38;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_38, 0);
x_89 = lean_ctor_get(x_38, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_38);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_31);
x_91 = lean_ctor_get(x_30, 1);
lean_inc(x_91);
lean_dec(x_30);
x_92 = lean_ctor_get(x_15, 1);
lean_inc(x_92);
lean_dec(x_15);
x_93 = lean_ctor_get(x_17, 1);
lean_inc(x_93);
lean_dec(x_17);
x_94 = lean_ctor_get(x_19, 1);
lean_inc(x_94);
lean_dec(x_19);
x_95 = lean_ctor_get(x_23, 1);
lean_inc(x_95);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_96 = l_Lean_Meta_Grind_mkEqTrueProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_97);
lean_inc(x_29);
x_99 = l_Lean_Meta_mkOfEqTrueCore(x_29, x_97);
lean_inc(x_93);
x_100 = l_Lean_Expr_app___override(x_93, x_99);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_101 = l_Lean_Meta_Grind_preprocess(x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_102);
x_104 = l_Lean_Meta_Simp_Result_getProof(x_102, x_6, x_7, x_8, x_9, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
lean_dec(x_102);
x_111 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_110);
x_112 = lean_grind_internalize(x_110, x_108, x_111, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_109);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_mk_string_unchecked("Lean", 4, 4);
x_115 = lean_mk_string_unchecked("Grind", 5, 5);
x_116 = lean_mk_string_unchecked("dite_cond_eq_true'", 18, 18);
x_117 = l_Lean_Name_mkStr3(x_114, x_115, x_116);
x_118 = l_Lean_Expr_constLevels_x21(x_25);
lean_dec(x_25);
x_119 = l_Lean_Expr_const___override(x_117, x_118);
lean_inc(x_110);
x_120 = l_Lean_mkApp8(x_119, x_95, x_29, x_94, x_93, x_92, x_110, x_97, x_105);
x_121 = lean_box(0);
x_122 = lean_unbox(x_121);
x_123 = l_Lean_Meta_Grind_pushEqCore(x_1, x_110, x_120, x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_113);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_123;
}
else
{
lean_dec(x_110);
lean_dec(x_105);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_112;
}
}
else
{
uint8_t x_124; 
lean_dec(x_102);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_104);
if (x_124 == 0)
{
return x_104;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_104, 0);
x_126 = lean_ctor_get(x_104, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_104);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_101);
if (x_128 == 0)
{
return x_101;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_101, 0);
x_130 = lean_ctor_get(x_101, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_101);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_96);
if (x_132 == 0)
{
return x_96;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_96, 0);
x_134 = lean_ctor_get(x_96, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_96);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_30);
if (x_136 == 0)
{
return x_30;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_30, 0);
x_138 = lean_ctor_get(x_30, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_30);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5689_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("dite", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDIte), 10, 0);
x_5 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_getRootENode___redArg(x_1, x_2, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*13 + 2);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_15, 1);
x_26 = lean_ctor_get(x_15, 0);
lean_dec(x_26);
lean_inc(x_1);
x_27 = l_Lean_Expr_cleanupAnnotations(x_1);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_free_object(x_15);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_25;
goto block_14;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_inc(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_15);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_25;
goto block_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_inc(x_29);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_32 = lean_mk_string_unchecked("Decidable", 9, 9);
x_33 = lean_mk_string_unchecked("decide", 6, 6);
x_34 = l_Lean_Name_mkStr2(x_32, x_33);
x_35 = l_Lean_Expr_isConstOf(x_31, x_34);
lean_dec(x_34);
lean_dec(x_31);
if (x_35 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_free_object(x_15);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_25;
goto block_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_mk_string_unchecked("Bool", 4, 4);
x_40 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_39);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = l_Lean_Expr_isConstOf(x_38, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_mk_string_unchecked("false", 5, 5);
x_44 = l_Lean_Name_mkStr2(x_39, x_43);
x_45 = l_Lean_Expr_isConstOf(x_38, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_box(0);
lean_ctor_set(x_15, 0, x_46);
return x_15;
}
else
{
lean_object* x_47; 
lean_free_object(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_47 = lean_grind_mk_eq_proof(x_1, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_mk_string_unchecked("Lean", 4, 4);
x_51 = lean_mk_string_unchecked("Grind", 5, 5);
x_52 = lean_mk_string_unchecked("of_decide_eq_false", 18, 18);
x_53 = l_Lean_Name_mkStr3(x_50, x_51, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_Expr_const___override(x_53, x_54);
lean_inc(x_37);
x_56 = l_Lean_mkApp3(x_55, x_37, x_36, x_48);
x_57 = l_Lean_Meta_Grind_pushEqFalse(x_37, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_39);
lean_free_object(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_62 = lean_grind_mk_eq_proof(x_1, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_mk_string_unchecked("Lean", 4, 4);
x_66 = lean_mk_string_unchecked("Grind", 5, 5);
x_67 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_68 = l_Lean_Name_mkStr3(x_65, x_66, x_67);
x_69 = lean_box(0);
x_70 = l_Lean_Expr_const___override(x_68, x_69);
lean_inc(x_37);
x_71 = l_Lean_mkApp3(x_70, x_37, x_36, x_63);
x_72 = l_Lean_Meta_Grind_pushEqTrue(x_37, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_64);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_62);
if (x_73 == 0)
{
return x_62;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_62, 0);
x_75 = lean_ctor_get(x_62, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_62);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_15, 1);
lean_inc(x_77);
lean_dec(x_15);
lean_inc(x_1);
x_78 = l_Lean_Expr_cleanupAnnotations(x_1);
x_79 = l_Lean_Expr_isApp(x_78);
if (x_79 == 0)
{
lean_dec(x_78);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_77;
goto block_14;
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_inc(x_78);
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_78);
x_81 = l_Lean_Expr_isApp(x_80);
if (x_81 == 0)
{
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_77;
goto block_14;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_inc(x_80);
x_82 = l_Lean_Expr_appFnCleanup___redArg(x_80);
x_83 = lean_mk_string_unchecked("Decidable", 9, 9);
x_84 = lean_mk_string_unchecked("decide", 6, 6);
x_85 = l_Lean_Name_mkStr2(x_83, x_84);
x_86 = l_Lean_Expr_isConstOf(x_82, x_85);
lean_dec(x_85);
lean_dec(x_82);
if (x_86 == 0)
{
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_77;
goto block_14;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_dec(x_78);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
lean_dec(x_80);
x_89 = lean_ctor_get(x_16, 0);
lean_inc(x_89);
lean_dec(x_16);
x_90 = lean_mk_string_unchecked("Bool", 4, 4);
x_91 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_90);
x_92 = l_Lean_Name_mkStr2(x_90, x_91);
x_93 = l_Lean_Expr_isConstOf(x_89, x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_mk_string_unchecked("false", 5, 5);
x_95 = l_Lean_Name_mkStr2(x_90, x_94);
x_96 = l_Lean_Expr_isConstOf(x_89, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_77);
return x_98;
}
else
{
lean_object* x_99; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_99 = lean_grind_mk_eq_proof(x_1, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_mk_string_unchecked("Lean", 4, 4);
x_103 = lean_mk_string_unchecked("Grind", 5, 5);
x_104 = lean_mk_string_unchecked("of_decide_eq_false", 18, 18);
x_105 = l_Lean_Name_mkStr3(x_102, x_103, x_104);
x_106 = lean_box(0);
x_107 = l_Lean_Expr_const___override(x_105, x_106);
lean_inc(x_88);
x_108 = l_Lean_mkApp3(x_107, x_88, x_87, x_100);
x_109 = l_Lean_Meta_Grind_pushEqFalse(x_88, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_99, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_112 = x_99;
} else {
 lean_dec_ref(x_99);
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
else
{
lean_object* x_114; 
lean_dec(x_90);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_114 = lean_grind_mk_eq_proof(x_1, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_mk_string_unchecked("Lean", 4, 4);
x_118 = lean_mk_string_unchecked("Grind", 5, 5);
x_119 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
x_120 = l_Lean_Name_mkStr3(x_117, x_118, x_119);
x_121 = lean_box(0);
x_122 = l_Lean_Expr_const___override(x_120, x_121);
lean_inc(x_88);
x_123 = l_Lean_mkApp3(x_122, x_88, x_87, x_115);
x_124 = l_Lean_Meta_Grind_pushEqTrue(x_88, x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_116);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = lean_ctor_get(x_114, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_114, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
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
uint8_t x_129; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_15);
if (x_129 == 0)
{
return x_15;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_15, 0);
x_131 = lean_ctor_get(x_15, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_15);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5969_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Decidable", 9, 9);
x_3 = lean_mk_string_unchecked("decide", 6, 6);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideDown), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateDecideUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = lean_mk_string_unchecked("Decidable", 9, 9);
x_21 = lean_mk_string_unchecked("decide", 6, 6);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = l_Lean_Expr_isConstOf(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
if (x_23 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l_Lean_Meta_Grind_isEqTrue___redArg(x_24, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
lean_inc(x_24);
x_30 = l_Lean_Meta_Grind_isEqFalse(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = l_Lean_Meta_Grind_getBoolFalseExpr___redArg(x_5, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_43 = l_Lean_Meta_Grind_mkEqFalseProof(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_mk_string_unchecked("Lean", 4, 4);
x_47 = lean_mk_string_unchecked("Grind", 5, 5);
x_48 = lean_mk_string_unchecked("decide_eq_false", 15, 15);
x_49 = l_Lean_Name_mkStr3(x_46, x_47, x_48);
x_50 = lean_box(0);
x_51 = l_Lean_Expr_const___override(x_49, x_50);
x_52 = l_Lean_mkApp3(x_51, x_24, x_29, x_44);
x_53 = lean_unbox(x_26);
lean_dec(x_26);
x_54 = l_Lean_Meta_Grind_pushEqCore(x_1, x_41, x_52, x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
return x_43;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_43);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_30);
if (x_59 == 0)
{
return x_30;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_30, 0);
x_61 = lean_ctor_get(x_30, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_30);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_26);
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
lean_dec(x_25);
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_dec(x_15);
x_65 = l_Lean_Meta_Grind_getBoolTrueExpr___redArg(x_5, x_63);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_68 = l_Lean_Meta_Grind_mkEqTrueProof(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_mk_string_unchecked("Lean", 4, 4);
x_72 = lean_mk_string_unchecked("Grind", 5, 5);
x_73 = lean_mk_string_unchecked("decide_eq_true", 14, 14);
x_74 = l_Lean_Name_mkStr3(x_71, x_72, x_73);
x_75 = lean_box(0);
x_76 = l_Lean_Expr_const___override(x_74, x_75);
x_77 = l_Lean_mkApp3(x_76, x_24, x_64, x_69);
x_78 = lean_box(0);
x_79 = lean_unbox(x_78);
x_80 = l_Lean_Meta_Grind_pushEqCore(x_1, x_66, x_77, x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_68);
if (x_81 == 0)
{
return x_68;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_68, 0);
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_68);
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
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_25);
if (x_85 == 0)
{
return x_25;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_25, 0);
x_87 = lean_ctor_get(x_25, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_25);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6264_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Decidable", 9, 9);
x_3 = lean_mk_string_unchecked("decide", 6, 6);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateDecideUp), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = lean_mk_string_unchecked("Bool", 4, 4);
x_21 = lean_mk_string_unchecked("and", 3, 3);
lean_inc(x_20);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = l_Lean_Expr_isConstOf(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
if (x_23 == 0)
{
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_24, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
lean_inc(x_29);
x_30 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_29, x_2, x_5, x_8, x_9, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_24);
x_34 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_24, x_2, x_5, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_29);
x_38 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_29, x_2, x_5, x_8, x_9, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_48 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Grind", 5, 5);
x_53 = lean_mk_string_unchecked("and_eq_of_eq_false_right", 24, 24);
x_54 = l_Lean_Name_mkStr4(x_51, x_52, x_20, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Expr_const___override(x_54, x_55);
x_57 = l_Lean_mkApp3(x_56, x_24, x_29, x_49);
x_58 = l_Lean_Meta_Grind_pushEqBoolFalse(x_1, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_48);
if (x_59 == 0)
{
return x_48;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
return x_38;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_38, 0);
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_38);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_34, 1);
lean_inc(x_67);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_68 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_mk_string_unchecked("Lean", 4, 4);
x_72 = lean_mk_string_unchecked("Grind", 5, 5);
x_73 = lean_mk_string_unchecked("and_eq_of_eq_false_left", 23, 23);
x_74 = l_Lean_Name_mkStr4(x_71, x_72, x_20, x_73);
x_75 = lean_box(0);
x_76 = l_Lean_Expr_const___override(x_74, x_75);
x_77 = l_Lean_mkApp3(x_76, x_24, x_29, x_69);
x_78 = l_Lean_Meta_Grind_pushEqBoolFalse(x_1, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_83; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_34);
if (x_83 == 0)
{
return x_34;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_34, 0);
x_85 = lean_ctor_get(x_34, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_34);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_30, 1);
lean_inc(x_87);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_88 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("Grind", 5, 5);
x_93 = lean_mk_string_unchecked("and_eq_of_eq_true_right", 23, 23);
x_94 = l_Lean_Name_mkStr4(x_91, x_92, x_20, x_93);
x_95 = lean_box(0);
x_96 = l_Lean_Expr_const___override(x_94, x_95);
lean_inc(x_24);
x_97 = l_Lean_mkApp3(x_96, x_24, x_29, x_89);
x_98 = lean_unbox(x_26);
lean_dec(x_26);
x_99 = l_Lean_Meta_Grind_pushEqCore(x_1, x_24, x_97, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_88);
if (x_100 == 0)
{
return x_88;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_88, 0);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_88);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_30);
if (x_104 == 0)
{
return x_30;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_30, 0);
x_106 = lean_ctor_get(x_30, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_30);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_26);
x_108 = lean_ctor_get(x_25, 1);
lean_inc(x_108);
lean_dec(x_25);
x_109 = lean_ctor_get(x_15, 1);
lean_inc(x_109);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_110 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_mk_string_unchecked("Lean", 4, 4);
x_114 = lean_mk_string_unchecked("Grind", 5, 5);
x_115 = lean_mk_string_unchecked("and_eq_of_eq_true_left", 22, 22);
x_116 = l_Lean_Name_mkStr4(x_113, x_114, x_20, x_115);
x_117 = lean_box(0);
x_118 = l_Lean_Expr_const___override(x_116, x_117);
lean_inc(x_109);
x_119 = l_Lean_mkApp3(x_118, x_24, x_109, x_111);
x_120 = lean_box(0);
x_121 = lean_unbox(x_120);
x_122 = l_Lean_Meta_Grind_pushEqCore(x_1, x_109, x_119, x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_112);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_122;
}
else
{
uint8_t x_123; 
lean_dec(x_109);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
return x_110;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_110, 0);
x_125 = lean_ctor_get(x_110, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_110);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_25);
if (x_127 == 0)
{
return x_25;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_25, 0);
x_129 = lean_ctor_get(x_25, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_25);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6645_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Bool", 4, 4);
x_3 = lean_mk_string_unchecked("and", 3, 3);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndUp), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolAndDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_inc(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("and", 3, 3);
lean_inc(x_30);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = l_Lean_Expr_isConstOf(x_29, x_32);
lean_dec(x_32);
lean_dec(x_29);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_34; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_mk_string_unchecked("Lean", 4, 4);
x_40 = lean_mk_string_unchecked("Grind", 5, 5);
x_41 = lean_mk_string_unchecked("eq_true_of_and_eq_true_left", 27, 27);
lean_inc(x_30);
lean_inc(x_40);
lean_inc(x_39);
x_42 = l_Lean_Name_mkStr4(x_39, x_40, x_30, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Expr_const___override(x_42, x_43);
lean_inc(x_35);
lean_inc(x_37);
lean_inc(x_38);
x_45 = l_Lean_mkApp3(x_44, x_38, x_37, x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_38);
x_46 = l_Lean_Meta_Grind_pushEqBoolTrue(x_38, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("eq_true_of_and_eq_true_right", 28, 28);
x_49 = l_Lean_Name_mkStr4(x_39, x_40, x_30, x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_43);
lean_inc(x_37);
x_51 = l_Lean_mkApp3(x_50, x_38, x_37, x_35);
x_52 = l_Lean_Meta_Grind_pushEqBoolTrue(x_37, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_46;
}
}
else
{
uint8_t x_53; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6866_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Bool", 4, 4);
x_3 = lean_mk_string_unchecked("and", 3, 3);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolAndDown), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = lean_mk_string_unchecked("Bool", 4, 4);
x_21 = lean_mk_string_unchecked("or", 2, 2);
lean_inc(x_20);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = l_Lean_Expr_isConstOf(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
if (x_23 == 0)
{
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
lean_inc(x_24);
x_25 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_24, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_dec(x_15);
lean_inc(x_29);
x_30 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_29, x_2, x_5, x_8, x_9, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_24);
x_34 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_24, x_2, x_5, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_29);
x_38 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_29, x_2, x_5, x_8, x_9, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_48 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Grind", 5, 5);
x_53 = lean_mk_string_unchecked("or_eq_of_eq_true_right", 22, 22);
x_54 = l_Lean_Name_mkStr4(x_51, x_52, x_20, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Expr_const___override(x_54, x_55);
x_57 = l_Lean_mkApp3(x_56, x_24, x_29, x_49);
x_58 = l_Lean_Meta_Grind_pushEqBoolTrue(x_1, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_48);
if (x_59 == 0)
{
return x_48;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
return x_38;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_38, 0);
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_38);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_34, 1);
lean_inc(x_67);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_68 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_mk_string_unchecked("Lean", 4, 4);
x_72 = lean_mk_string_unchecked("Grind", 5, 5);
x_73 = lean_mk_string_unchecked("or_eq_of_eq_true_left", 21, 21);
x_74 = l_Lean_Name_mkStr4(x_71, x_72, x_20, x_73);
x_75 = lean_box(0);
x_76 = l_Lean_Expr_const___override(x_74, x_75);
x_77 = l_Lean_mkApp3(x_76, x_24, x_29, x_69);
x_78 = l_Lean_Meta_Grind_pushEqBoolTrue(x_1, x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_83; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_34);
if (x_83 == 0)
{
return x_34;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_34, 0);
x_85 = lean_ctor_get(x_34, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_34);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_30, 1);
lean_inc(x_87);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_29);
x_88 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("Grind", 5, 5);
x_93 = lean_mk_string_unchecked("or_eq_of_eq_false_right", 23, 23);
x_94 = l_Lean_Name_mkStr4(x_91, x_92, x_20, x_93);
x_95 = lean_box(0);
x_96 = l_Lean_Expr_const___override(x_94, x_95);
lean_inc(x_24);
x_97 = l_Lean_mkApp3(x_96, x_24, x_29, x_89);
x_98 = lean_unbox(x_26);
lean_dec(x_26);
x_99 = l_Lean_Meta_Grind_pushEqCore(x_1, x_24, x_97, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_88);
if (x_100 == 0)
{
return x_88;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_88, 0);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_88);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_30);
if (x_104 == 0)
{
return x_30;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_30, 0);
x_106 = lean_ctor_get(x_30, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_30);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_26);
x_108 = lean_ctor_get(x_25, 1);
lean_inc(x_108);
lean_dec(x_25);
x_109 = lean_ctor_get(x_15, 1);
lean_inc(x_109);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_110 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_mk_string_unchecked("Lean", 4, 4);
x_114 = lean_mk_string_unchecked("Grind", 5, 5);
x_115 = lean_mk_string_unchecked("or_eq_of_eq_false_left", 22, 22);
x_116 = l_Lean_Name_mkStr4(x_113, x_114, x_20, x_115);
x_117 = lean_box(0);
x_118 = l_Lean_Expr_const___override(x_116, x_117);
lean_inc(x_109);
x_119 = l_Lean_mkApp3(x_118, x_24, x_109, x_111);
x_120 = lean_box(0);
x_121 = lean_unbox(x_120);
x_122 = l_Lean_Meta_Grind_pushEqCore(x_1, x_109, x_119, x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_112);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_122;
}
else
{
uint8_t x_123; 
lean_dec(x_109);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
return x_110;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_110, 0);
x_125 = lean_ctor_get(x_110, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_110);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_25);
if (x_127 == 0)
{
return x_25;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_25, 0);
x_129 = lean_ctor_get(x_25, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_25);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7247_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Bool", 4, 4);
x_3 = lean_mk_string_unchecked("or", 2, 2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrUp), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolOrDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_inc(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = lean_mk_string_unchecked("Bool", 4, 4);
x_31 = lean_mk_string_unchecked("or", 2, 2);
lean_inc(x_30);
x_32 = l_Lean_Name_mkStr2(x_30, x_31);
x_33 = l_Lean_Expr_isConstOf(x_29, x_32);
lean_dec(x_32);
lean_dec(x_29);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_34; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_mk_string_unchecked("Lean", 4, 4);
x_40 = lean_mk_string_unchecked("Grind", 5, 5);
x_41 = lean_mk_string_unchecked("eq_false_of_or_eq_false_left", 28, 28);
lean_inc(x_30);
lean_inc(x_40);
lean_inc(x_39);
x_42 = l_Lean_Name_mkStr4(x_39, x_40, x_30, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Expr_const___override(x_42, x_43);
lean_inc(x_35);
lean_inc(x_37);
lean_inc(x_38);
x_45 = l_Lean_mkApp3(x_44, x_38, x_37, x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_38);
x_46 = l_Lean_Meta_Grind_pushEqBoolFalse(x_38, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("eq_false_of_or_eq_false_right", 29, 29);
x_49 = l_Lean_Name_mkStr4(x_39, x_40, x_30, x_48);
x_50 = l_Lean_Expr_const___override(x_49, x_43);
lean_inc(x_37);
x_51 = l_Lean_mkApp3(x_50, x_38, x_37, x_35);
x_52 = l_Lean_Meta_Grind_pushEqBoolFalse(x_37, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_46;
}
}
else
{
uint8_t x_53; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7468_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Bool", 4, 4);
x_3 = lean_mk_string_unchecked("or", 2, 2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolOrDown), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = lean_mk_string_unchecked("Bool", 4, 4);
x_19 = lean_mk_string_unchecked("not", 3, 3);
lean_inc(x_18);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
lean_inc(x_22);
x_23 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_22, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_22);
x_27 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_22, x_2, x_5, x_8, x_9, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_22, x_2, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_22);
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
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_22);
x_41 = lean_grind_mk_eq_proof(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_mk_string_unchecked("Lean", 4, 4);
x_45 = lean_mk_string_unchecked("Grind", 5, 5);
x_46 = lean_mk_string_unchecked("false_of_not_eq_self", 20, 20);
x_47 = l_Lean_Name_mkStr4(x_44, x_45, x_18, x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Expr_const___override(x_47, x_48);
x_50 = l_Lean_mkAppB(x_49, x_22, x_42);
x_51 = l_Lean_Meta_Grind_closeGoal(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_22);
x_57 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_mk_string_unchecked("Lean", 4, 4);
x_61 = lean_mk_string_unchecked("Grind", 5, 5);
x_62 = lean_mk_string_unchecked("not_eq_of_eq_true", 17, 17);
x_63 = l_Lean_Name_mkStr4(x_60, x_61, x_18, x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Expr_const___override(x_63, x_64);
x_66 = l_Lean_mkAppB(x_65, x_22, x_58);
x_67 = l_Lean_Meta_Grind_pushEqBoolFalse(x_1, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_22);
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
x_68 = !lean_is_exclusive(x_57);
if (x_68 == 0)
{
return x_57;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_57, 0);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_22);
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
x_72 = !lean_is_exclusive(x_27);
if (x_72 == 0)
{
return x_27;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_27, 0);
x_74 = lean_ctor_get(x_27, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_27);
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
x_76 = lean_ctor_get(x_23, 1);
lean_inc(x_76);
lean_dec(x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_22);
x_77 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_mk_string_unchecked("Lean", 4, 4);
x_81 = lean_mk_string_unchecked("Grind", 5, 5);
x_82 = lean_mk_string_unchecked("not_eq_of_eq_false", 18, 18);
x_83 = l_Lean_Name_mkStr4(x_80, x_81, x_18, x_82);
x_84 = lean_box(0);
x_85 = l_Lean_Expr_const___override(x_83, x_84);
x_86 = l_Lean_mkAppB(x_85, x_22, x_78);
x_87 = l_Lean_Meta_Grind_pushEqBoolTrue(x_1, x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_79);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_22);
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
x_88 = !lean_is_exclusive(x_77);
if (x_88 == 0)
{
return x_77;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_77, 0);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_77);
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
uint8_t x_92; 
lean_dec(x_22);
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
x_92 = !lean_is_exclusive(x_23);
if (x_92 == 0)
{
return x_23;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_23, 0);
x_94 = lean_ctor_get(x_23, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_23);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7748_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Bool", 4, 4);
x_3 = lean_mk_string_unchecked("not", 3, 3);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotUp), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBoolNotDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = lean_mk_string_unchecked("Bool", 4, 4);
x_19 = lean_mk_string_unchecked("not", 3, 3);
lean_inc(x_18);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_22; 
lean_inc(x_1);
x_22 = l_Lean_Meta_Grind_isEqBoolFalse___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
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
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
lean_inc(x_1);
x_27 = l_Lean_Meta_Grind_isEqBoolTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_26, x_2, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_26);
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
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_26);
x_41 = lean_grind_mk_eq_proof(x_1, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_mk_string_unchecked("Lean", 4, 4);
x_45 = lean_mk_string_unchecked("Grind", 5, 5);
x_46 = lean_mk_string_unchecked("false_of_not_eq_self", 20, 20);
x_47 = l_Lean_Name_mkStr4(x_44, x_45, x_18, x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Expr_const___override(x_47, x_48);
x_50 = l_Lean_mkAppB(x_49, x_26, x_42);
x_51 = l_Lean_Meta_Grind_closeGoal(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_57 = l_Lean_Meta_Grind_mkEqBoolTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_mk_string_unchecked("Lean", 4, 4);
x_61 = lean_mk_string_unchecked("Grind", 5, 5);
x_62 = lean_mk_string_unchecked("eq_false_of_not_eq_true", 23, 23);
x_63 = l_Lean_Name_mkStr4(x_60, x_61, x_18, x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Expr_const___override(x_63, x_64);
lean_inc(x_26);
x_66 = l_Lean_mkAppB(x_65, x_26, x_58);
x_67 = l_Lean_Meta_Grind_pushEqBoolFalse(x_26, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_57);
if (x_68 == 0)
{
return x_57;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_57, 0);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_26);
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
x_72 = !lean_is_exclusive(x_27);
if (x_72 == 0)
{
return x_27;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_27, 0);
x_74 = lean_ctor_get(x_27, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_27);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_22, 1);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_ctor_get(x_15, 1);
lean_inc(x_77);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_78 = l_Lean_Meta_Grind_mkEqBoolFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_mk_string_unchecked("Lean", 4, 4);
x_82 = lean_mk_string_unchecked("Grind", 5, 5);
x_83 = lean_mk_string_unchecked("eq_true_of_not_eq_false", 23, 23);
x_84 = l_Lean_Name_mkStr4(x_81, x_82, x_18, x_83);
x_85 = lean_box(0);
x_86 = l_Lean_Expr_const___override(x_84, x_85);
lean_inc(x_77);
x_87 = l_Lean_mkAppB(x_86, x_77, x_79);
x_88 = l_Lean_Meta_Grind_pushEqBoolTrue(x_77, x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_77);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_78);
if (x_89 == 0)
{
return x_78;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_78, 0);
x_91 = lean_ctor_get(x_78, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_78);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_22);
if (x_93 == 0)
{
return x_22;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_22, 0);
x_95 = lean_ctor_get(x_22, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_22);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
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
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_8028_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Bool", 4, 4);
x_3 = lean_mk_string_unchecked("not", 3, 3);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBoolNotDown), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateAndUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_383_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateAndDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_604_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateOrUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_985_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateOrDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1206_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateNotUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1486_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateNotDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_1766_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_2729_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateEqDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_3463_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateBEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_3906_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateEqMatchDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4184_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateHEqDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4439_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateHEqUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_4695_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateIte_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5149_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateDIte_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5689_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateDecideDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_5969_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateDecideUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6264_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateBoolAndUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6645_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateBoolAndDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_6866_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateBoolOrUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7247_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateBoolOrDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7468_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateBoolNotUp_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_7748_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_propagateBoolNotDown_declare__1____x40_Lean_Meta_Tactic_Grind_Propagate___hyg_8028_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
