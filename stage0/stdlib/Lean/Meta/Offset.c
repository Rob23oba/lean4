// Lean compiler output
// Module: Lean.Meta.Offset
// Imports: Init.Control.Option Lean.Data.LBool Lean.Meta.InferType Lean.Meta.NatInstTesters Lean.Util.SafeExponentiation
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
lean_object* l_Lean_Meta_isInstHMulNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstAddNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
extern lean_object* l_Lean_Nat_mkInstAdd;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstModNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__9(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstOfNatNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__11(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHPowNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_expr_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDivNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstNatPowNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHAdd;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__3(lean_object*, lean_object*);
lean_object* l_OptionT_instMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_evalPow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_isInstSubNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHModNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHSubNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHDivNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__6(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstPowNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__1), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
else
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__3), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__4), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__6), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__7), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__9), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__11), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
x_17 = lean_st_ref_set(x_3, x_16, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__14(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__13___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_OptionT_instMonadLift(lean_box(0), x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__0___boxed), 5, 0);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__2), 4, 0);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__5), 4, 0);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__8), 4, 0);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__10), 4, 0);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__12), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_18 = l_instMonadEIO(lean_box(0));
x_19 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_21);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, lean_box(0));
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_33, 0, x_32);
lean_inc(x_33);
lean_inc(x_30);
lean_inc(x_27);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_16);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_17);
x_36 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_38);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_27);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_30);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_33);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_14);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_45);
lean_ctor_set(x_48, 4, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_15);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__14), 2, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_12);
lean_inc(x_49);
x_52 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_52, 0, lean_box(0));
lean_closure_set(x_52, 1, x_49);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_11);
lean_ctor_set(x_53, 3, x_10);
lean_ctor_set(x_53, 4, x_9);
lean_inc(x_49);
x_54 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_54, 0, lean_box(0));
lean_closure_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_OptionT_instMonadLift(lean_box(0), x_49);
x_57 = lean_apply_2(x_56, lean_box(0), x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
x_59 = l_Lean_instantiateMVars___redArg(x_55, x_58, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = lean_apply_5(x_59, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_ctor_set(x_60, 0, x_64);
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_60, 1);
x_70 = lean_ctor_get(x_60, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_61, 0);
lean_inc(x_71);
lean_dec(x_61);
x_72 = l_Lean_Expr_getAppFn(x_71);
x_73 = l_Lean_Expr_isMVar(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_free_object(x_60);
x_74 = lean_apply_6(x_2, x_71, x_3, x_4, x_5, x_6, x_69);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_box(0);
lean_ctor_set(x_60, 0, x_75);
return x_60;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_dec(x_60);
x_77 = lean_ctor_get(x_61, 0);
lean_inc(x_77);
lean_dec(x_61);
x_78 = l_Lean_Expr_getAppFn(x_77);
x_79 = l_Lean_Expr_isMVar(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_apply_6(x_2, x_77, x_3, x_4, x_5, x_6, x_76);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_60);
if (x_83 == 0)
{
return x_60;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_60, 0);
x_85 = lean_ctor_get(x_60, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_60);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__0___boxed), 5, 0);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__2), 4, 0);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__5), 4, 0);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__8), 4, 0);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__10), 4, 0);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__12), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_19 = l_instMonadEIO(lean_box(0));
x_20 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_34, 0, x_33);
lean_inc(x_34);
lean_inc(x_31);
lean_inc(x_28);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_17);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
x_37 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_39);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_28);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_31);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_34);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_15);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_46);
lean_ctor_set(x_49, 4, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_16);
lean_inc(x_50);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__14), 2, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_13);
lean_inc(x_50);
x_53 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_53, 0, lean_box(0));
lean_closure_set(x_53, 1, x_50);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_12);
lean_ctor_set(x_54, 3, x_11);
lean_ctor_set(x_54, 4, x_10);
lean_inc(x_50);
x_55 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_OptionT_instMonadLift(lean_box(0), x_50);
x_58 = lean_apply_2(x_57, lean_box(0), x_9);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
x_60 = l_Lean_instantiateMVars___redArg(x_56, x_59, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = lean_apply_5(x_60, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set(x_61, 0, x_65);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_61, 1);
x_71 = lean_ctor_get(x_61, 0);
lean_dec(x_71);
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
lean_dec(x_62);
x_73 = l_Lean_Expr_getAppFn(x_72);
x_74 = l_Lean_Expr_isMVar(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_free_object(x_61);
x_75 = lean_apply_6(x_3, x_72, x_4, x_5, x_6, x_7, x_70);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_76 = lean_box(0);
lean_ctor_set(x_61, 0, x_76);
return x_61;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_61, 1);
lean_inc(x_77);
lean_dec(x_61);
x_78 = lean_ctor_get(x_62, 0);
lean_inc(x_78);
lean_dec(x_62);
x_79 = l_Lean_Expr_getAppFn(x_78);
x_80 = l_Lean_Expr_isMVar(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_apply_6(x_3, x_78, x_4, x_5, x_6, x_7, x_77);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
return x_61;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_61, 0);
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_61);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Offset_0__Lean_Meta_withInstantiatedMVars___redArg___lam__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_evalPow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_11);
x_12 = l_Lean_checkExponent(x_11, x_5, x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_Meta_evalNat(x_1, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_11);
return x_22;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_nat_pow(x_27, x_11);
lean_dec(x_11);
lean_dec(x_27);
lean_ctor_set(x_23, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_nat_pow(x_29, x_11);
lean_dec(x_11);
lean_dec(x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_34 = x_23;
} else {
 lean_dec_ref(x_23);
 x_34 = lean_box(0);
}
x_35 = lean_nat_pow(x_33, x_11);
lean_dec(x_11);
lean_dec(x_33);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
else
{
lean_dec(x_11);
return x_22;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_evalNat___lam__0___boxed), 6, 0);
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_8; 
lean_dec(x_7);
x_8 = l_Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_12 = l_Lean_Expr_const___override(x_11, x_10);
x_13 = l_Lean_Meta_evalNat___lam__0(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_12);
return x_13;
}
case 1:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lean_Name_str___override(x_11, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_10);
x_18 = l_Lean_Meta_evalNat___lam__0(x_17, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_17);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_39; lean_object* x_42; uint8_t x_43; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_42 = lean_mk_string_unchecked("Nat", 3, 3);
x_43 = lean_string_dec_eq(x_21, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_inc(x_21);
x_44 = l_Lean_Name_str___override(x_11, x_21);
lean_inc(x_19);
x_45 = l_Lean_Name_str___override(x_44, x_19);
lean_inc(x_10);
x_46 = l_Lean_Expr_const___override(x_45, x_10);
x_39 = x_46;
goto block_41;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_mk_string_unchecked("zero", 4, 4);
x_48 = lean_string_dec_eq(x_19, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l_Lean_Name_str___override(x_11, x_42);
lean_inc(x_19);
x_50 = l_Lean_Name_str___override(x_49, x_19);
lean_inc(x_10);
x_51 = l_Lean_Expr_const___override(x_50, x_10);
x_39 = x_51;
goto block_41;
}
else
{
lean_object* x_52; 
lean_dec(x_42);
lean_dec(x_7);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_evalNat___lam__2___boxed), 5, 0);
x_22 = x_52;
goto block_38;
}
}
block_38:
{
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
x_23 = lean_apply_5(x_22, x_2, x_3, x_4, x_5, x_6);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Lean_Name_str___override(x_24, x_25);
x_27 = l_Lean_Name_str___override(x_26, x_21);
x_28 = l_Lean_Name_str___override(x_27, x_19);
x_29 = l_Lean_Expr_const___override(x_28, x_10);
x_30 = l_Lean_Meta_evalNat___lam__0(x_29, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_29);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_22);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = l_Lean_Name_num___override(x_31, x_32);
x_34 = l_Lean_Name_str___override(x_33, x_21);
x_35 = l_Lean_Name_str___override(x_34, x_19);
x_36 = l_Lean_Expr_const___override(x_35, x_10);
x_37 = l_Lean_Meta_evalNat___lam__0(x_36, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_36);
return x_37;
}
}
}
block_41:
{
lean_object* x_40; 
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_evalNat___lam__1), 7, 2);
lean_closure_set(x_40, 0, x_7);
lean_closure_set(x_40, 1, x_39);
x_22 = x_40;
goto block_38;
}
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_7);
x_53 = lean_ctor_get(x_9, 1);
lean_inc(x_53);
lean_dec(x_9);
x_54 = lean_ctor_get(x_14, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_dec(x_14);
x_56 = l_Lean_Name_num___override(x_54, x_55);
x_57 = l_Lean_Name_str___override(x_56, x_53);
x_58 = l_Lean_Expr_const___override(x_57, x_10);
x_59 = l_Lean_Meta_evalNat___lam__0(x_58, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_58);
return x_59;
}
}
}
default: 
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
x_60 = lean_ctor_get(x_9, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_9, 1);
lean_inc(x_61);
lean_dec(x_9);
x_62 = l_Lean_Name_num___override(x_60, x_61);
x_63 = l_Lean_Expr_const___override(x_62, x_10);
x_64 = l_Lean_Meta_evalNat___lam__0(x_63, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_63);
return x_64;
}
}
}
case 5:
{
lean_object* x_65; 
lean_dec(x_7);
x_65 = l_Lean_Meta_evalNat_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_65;
}
case 9:
{
lean_object* x_66; 
lean_dec(x_7);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_ctor_set_tag(x_66, 1);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_6);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_Expr_lit___override(x_66);
x_73 = l_Lean_Meta_evalNat___lam__0(x_72, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_72);
return x_73;
}
}
case 10:
{
lean_object* x_74; 
lean_dec(x_7);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
lean_dec(x_1);
x_1 = x_74;
goto _start;
}
default: 
{
lean_object* x_76; 
lean_dec(x_7);
x_76 = l_Lean_Meta_evalNat___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = lean_mk_string_unchecked("Nat", 3, 3);
x_19 = lean_mk_string_unchecked("succ", 4, 4);
lean_inc(x_18);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isApp(x_17);
if (x_22 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_25 = lean_mk_string_unchecked("pow", 3, 3);
lean_inc(x_25);
lean_inc(x_18);
x_26 = l_Lean_Name_mkStr2(x_18, x_25);
x_27 = l_Lean_Expr_isConstOf(x_24, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_mk_string_unchecked("mod", 3, 3);
lean_inc(x_28);
lean_inc(x_18);
x_29 = l_Lean_Name_mkStr2(x_18, x_28);
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_mk_string_unchecked("div", 3, 3);
lean_inc(x_31);
lean_inc(x_18);
x_32 = l_Lean_Name_mkStr2(x_18, x_31);
x_33 = l_Lean_Expr_isConstOf(x_24, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_mk_string_unchecked("mul", 3, 3);
lean_inc(x_34);
lean_inc(x_18);
x_35 = l_Lean_Name_mkStr2(x_18, x_34);
x_36 = l_Lean_Expr_isConstOf(x_24, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_mk_string_unchecked("sub", 3, 3);
lean_inc(x_37);
lean_inc(x_18);
x_38 = l_Lean_Name_mkStr2(x_18, x_37);
x_39 = l_Lean_Expr_isConstOf(x_24, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_mk_string_unchecked("add", 3, 3);
lean_inc(x_40);
x_41 = l_Lean_Name_mkStr2(x_18, x_40);
x_42 = l_Lean_Expr_isConstOf(x_24, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_isApp(x_24);
if (x_43 == 0)
{
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_inc(x_24);
x_44 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_45 = lean_mk_string_unchecked("OfNat", 5, 5);
x_46 = lean_mk_string_unchecked("ofNat", 5, 5);
x_47 = l_Lean_Name_mkStr2(x_45, x_46);
x_48 = l_Lean_Expr_isConstOf(x_44, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isApp(x_44);
if (x_49 == 0)
{
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_dec(x_24);
x_51 = l_Lean_Expr_appFnCleanup___redArg(x_44);
x_52 = lean_mk_string_unchecked("NatPow", 6, 6);
lean_inc(x_25);
x_53 = l_Lean_Name_mkStr2(x_52, x_25);
x_54 = l_Lean_Expr_isConstOf(x_51, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_mk_string_unchecked("Mod", 3, 3);
x_56 = l_Lean_Name_mkStr2(x_55, x_28);
x_57 = l_Lean_Expr_isConstOf(x_51, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_mk_string_unchecked("Div", 3, 3);
x_59 = l_Lean_Name_mkStr2(x_58, x_31);
x_60 = l_Lean_Expr_isConstOf(x_51, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_mk_string_unchecked("Mul", 3, 3);
x_62 = l_Lean_Name_mkStr2(x_61, x_34);
x_63 = l_Lean_Expr_isConstOf(x_51, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_mk_string_unchecked("Sub", 3, 3);
x_65 = l_Lean_Name_mkStr2(x_64, x_37);
x_66 = l_Lean_Expr_isConstOf(x_51, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_mk_string_unchecked("Add", 3, 3);
x_68 = l_Lean_Name_mkStr2(x_67, x_40);
x_69 = l_Lean_Expr_isConstOf(x_51, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isApp(x_51);
if (x_70 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = l_Lean_Expr_appFnCleanup___redArg(x_51);
x_72 = lean_mk_string_unchecked("Pow", 3, 3);
x_73 = l_Lean_Name_mkStr2(x_72, x_25);
x_74 = l_Lean_Expr_isConstOf(x_71, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_isApp(x_71);
if (x_75 == 0)
{
lean_dec(x_71);
lean_dec(x_50);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = l_Lean_Expr_appFnCleanup___redArg(x_71);
x_77 = lean_mk_string_unchecked("HPow", 4, 4);
x_78 = lean_mk_string_unchecked("hPow", 4, 4);
x_79 = l_Lean_Name_mkStr2(x_77, x_78);
x_80 = l_Lean_Expr_isConstOf(x_76, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_mk_string_unchecked("HMod", 4, 4);
x_82 = lean_mk_string_unchecked("hMod", 4, 4);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
x_84 = l_Lean_Expr_isConstOf(x_76, x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_mk_string_unchecked("HDiv", 4, 4);
x_86 = lean_mk_string_unchecked("hDiv", 4, 4);
x_87 = l_Lean_Name_mkStr2(x_85, x_86);
x_88 = l_Lean_Expr_isConstOf(x_76, x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_mk_string_unchecked("HMul", 4, 4);
x_90 = lean_mk_string_unchecked("hMul", 4, 4);
x_91 = l_Lean_Name_mkStr2(x_89, x_90);
x_92 = l_Lean_Expr_isConstOf(x_76, x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_mk_string_unchecked("HSub", 4, 4);
x_94 = lean_mk_string_unchecked("hSub", 4, 4);
x_95 = l_Lean_Name_mkStr2(x_93, x_94);
x_96 = l_Lean_Expr_isConstOf(x_76, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_mk_string_unchecked("HAdd", 4, 4);
x_98 = lean_mk_string_unchecked("hAdd", 4, 4);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
x_100 = l_Lean_Expr_isConstOf(x_76, x_99);
lean_dec(x_99);
lean_dec(x_76);
if (x_100 == 0)
{
lean_dec(x_50);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_10);
x_101 = l_Lean_Meta_isInstHAddNat(x_50, x_2, x_3, x_4, x_5, x_9);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
uint8_t x_104; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_101, 0);
lean_dec(x_105);
x_106 = lean_box(0);
lean_ctor_set(x_101, 0, x_106);
return x_101;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_dec(x_101);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_111 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_dec(x_114);
return x_115;
}
else
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_115, 0);
lean_dec(x_118);
x_119 = !lean_is_exclusive(x_116);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_116, 0);
x_121 = lean_nat_add(x_114, x_120);
lean_dec(x_120);
lean_dec(x_114);
lean_ctor_set(x_116, 0, x_121);
return x_115;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_116, 0);
lean_inc(x_122);
lean_dec(x_116);
x_123 = lean_nat_add(x_114, x_122);
lean_dec(x_122);
lean_dec(x_114);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_115, 0, x_124);
return x_115;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_115, 1);
lean_inc(x_125);
lean_dec(x_115);
x_126 = lean_ctor_get(x_116, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_127 = x_116;
} else {
 lean_dec_ref(x_116);
 x_127 = lean_box(0);
}
x_128 = lean_nat_add(x_114, x_126);
lean_dec(x_126);
lean_dec(x_114);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
return x_130;
}
}
}
else
{
lean_dec(x_114);
return x_115;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_111;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_76);
lean_dec(x_10);
x_131 = l_Lean_Meta_isInstHSubNat___redArg(x_50, x_3, x_9);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
uint8_t x_134; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_131);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_131, 0);
lean_dec(x_135);
x_136 = lean_box(0);
lean_ctor_set(x_131, 0, x_136);
return x_131;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_dec(x_131);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_131, 1);
lean_inc(x_140);
lean_dec(x_131);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_141 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_dec(x_144);
return x_145;
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_145);
if (x_147 == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_145, 0);
lean_dec(x_148);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_146, 0);
x_151 = lean_nat_sub(x_144, x_150);
lean_dec(x_150);
lean_dec(x_144);
lean_ctor_set(x_146, 0, x_151);
return x_145;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_146, 0);
lean_inc(x_152);
lean_dec(x_146);
x_153 = lean_nat_sub(x_144, x_152);
lean_dec(x_152);
lean_dec(x_144);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_145, 0, x_154);
return x_145;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_145, 1);
lean_inc(x_155);
lean_dec(x_145);
x_156 = lean_ctor_get(x_146, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_157 = x_146;
} else {
 lean_dec_ref(x_146);
 x_157 = lean_box(0);
}
x_158 = lean_nat_sub(x_144, x_156);
lean_dec(x_156);
lean_dec(x_144);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_155);
return x_160;
}
}
}
else
{
lean_dec(x_144);
return x_145;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_141;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_76);
lean_dec(x_10);
x_161 = l_Lean_Meta_isInstHMulNat___redArg(x_50, x_3, x_9);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
uint8_t x_164; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_161);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_161, 0);
lean_dec(x_165);
x_166 = lean_box(0);
lean_ctor_set(x_161, 0, x_166);
return x_161;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
lean_dec(x_161);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_161, 1);
lean_inc(x_170);
lean_dec(x_161);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_171 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_171;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_173);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_dec(x_174);
return x_175;
}
else
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_175);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_175, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_176, 0);
x_181 = lean_nat_mul(x_174, x_180);
lean_dec(x_180);
lean_dec(x_174);
lean_ctor_set(x_176, 0, x_181);
return x_175;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
lean_dec(x_176);
x_183 = lean_nat_mul(x_174, x_182);
lean_dec(x_182);
lean_dec(x_174);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_175, 0, x_184);
return x_175;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_ctor_get(x_175, 1);
lean_inc(x_185);
lean_dec(x_175);
x_186 = lean_ctor_get(x_176, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_187 = x_176;
} else {
 lean_dec_ref(x_176);
 x_187 = lean_box(0);
}
x_188 = lean_nat_mul(x_174, x_186);
lean_dec(x_186);
lean_dec(x_174);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_185);
return x_190;
}
}
}
else
{
lean_dec(x_174);
return x_175;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_171;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_76);
lean_dec(x_10);
x_191 = l_Lean_Meta_isInstHDivNat___redArg(x_50, x_3, x_9);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_unbox(x_192);
lean_dec(x_192);
if (x_193 == 0)
{
uint8_t x_194; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_194 = !lean_is_exclusive(x_191);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_191, 0);
lean_dec(x_195);
x_196 = lean_box(0);
lean_ctor_set(x_191, 0, x_196);
return x_191;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_191, 1);
lean_inc(x_197);
lean_dec(x_191);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_191, 1);
lean_inc(x_200);
lean_dec(x_191);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_201 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_obj_tag(x_202) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_201;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
lean_dec(x_202);
x_205 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_203);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
lean_dec(x_204);
return x_205;
}
else
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_205);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_205, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_206, 0);
x_211 = lean_nat_div(x_204, x_210);
lean_dec(x_210);
lean_dec(x_204);
lean_ctor_set(x_206, 0, x_211);
return x_205;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_206, 0);
lean_inc(x_212);
lean_dec(x_206);
x_213 = lean_nat_div(x_204, x_212);
lean_dec(x_212);
lean_dec(x_204);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_205, 0, x_214);
return x_205;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_ctor_get(x_205, 1);
lean_inc(x_215);
lean_dec(x_205);
x_216 = lean_ctor_get(x_206, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_217 = x_206;
} else {
 lean_dec_ref(x_206);
 x_217 = lean_box(0);
}
x_218 = lean_nat_div(x_204, x_216);
lean_dec(x_216);
lean_dec(x_204);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_215);
return x_220;
}
}
}
else
{
lean_dec(x_204);
return x_205;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_201;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_76);
lean_dec(x_10);
x_221 = l_Lean_Meta_isInstHModNat___redArg(x_50, x_3, x_9);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
uint8_t x_224; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_224 = !lean_is_exclusive(x_221);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_221, 0);
lean_dec(x_225);
x_226 = lean_box(0);
lean_ctor_set(x_221, 0, x_226);
return x_221;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_221, 1);
lean_inc(x_227);
lean_dec(x_221);
x_228 = lean_box(0);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_221, 1);
lean_inc(x_230);
lean_dec(x_221);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_231 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_231;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_233);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
lean_dec(x_234);
return x_235;
}
else
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_235);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; 
x_238 = lean_ctor_get(x_235, 0);
lean_dec(x_238);
x_239 = !lean_is_exclusive(x_236);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_236, 0);
x_241 = lean_nat_mod(x_234, x_240);
lean_dec(x_240);
lean_dec(x_234);
lean_ctor_set(x_236, 0, x_241);
return x_235;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_236, 0);
lean_inc(x_242);
lean_dec(x_236);
x_243 = lean_nat_mod(x_234, x_242);
lean_dec(x_242);
lean_dec(x_234);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_235, 0, x_244);
return x_235;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_245 = lean_ctor_get(x_235, 1);
lean_inc(x_245);
lean_dec(x_235);
x_246 = lean_ctor_get(x_236, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_247 = x_236;
} else {
 lean_dec_ref(x_236);
 x_247 = lean_box(0);
}
x_248 = lean_nat_mod(x_234, x_246);
lean_dec(x_246);
lean_dec(x_234);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(1, 1, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_245);
return x_250;
}
}
}
else
{
lean_dec(x_234);
return x_235;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_231;
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec(x_76);
lean_dec(x_10);
x_251 = l_Lean_Meta_isInstHPowNat___redArg(x_50, x_3, x_9);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_unbox(x_252);
lean_dec(x_252);
if (x_253 == 0)
{
uint8_t x_254; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_254 = !lean_is_exclusive(x_251);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_251, 0);
lean_dec(x_255);
x_256 = lean_box(0);
lean_ctor_set(x_251, 0, x_256);
return x_251;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_251, 1);
lean_inc(x_257);
lean_dec(x_251);
x_258 = lean_box(0);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_251, 1);
lean_inc(x_260);
lean_dec(x_251);
x_261 = l_Lean_Meta_evalNat_evalPow(x_23, x_16, x_2, x_3, x_4, x_5, x_260);
return x_261;
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
lean_dec(x_71);
lean_dec(x_10);
x_262 = l_Lean_Meta_isInstPowNat___redArg(x_50, x_3, x_9);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_unbox(x_263);
lean_dec(x_263);
if (x_264 == 0)
{
uint8_t x_265; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_265 = !lean_is_exclusive(x_262);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_262, 0);
lean_dec(x_266);
x_267 = lean_box(0);
lean_ctor_set(x_262, 0, x_267);
return x_262;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_262, 1);
lean_inc(x_268);
lean_dec(x_262);
x_269 = lean_box(0);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_262, 1);
lean_inc(x_271);
lean_dec(x_262);
x_272 = l_Lean_Meta_evalNat_evalPow(x_23, x_16, x_2, x_3, x_4, x_5, x_271);
return x_272;
}
}
}
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
lean_dec(x_51);
lean_dec(x_25);
lean_dec(x_10);
x_273 = l_Lean_Meta_isInstAddNat___redArg(x_50, x_3, x_9);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_unbox(x_274);
lean_dec(x_274);
if (x_275 == 0)
{
uint8_t x_276; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_276 = !lean_is_exclusive(x_273);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_273, 0);
lean_dec(x_277);
x_278 = lean_box(0);
lean_ctor_set(x_273, 0, x_278);
return x_273;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_273, 1);
lean_inc(x_279);
lean_dec(x_273);
x_280 = lean_box(0);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_273, 1);
lean_inc(x_282);
lean_dec(x_273);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_283 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_283;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
lean_dec(x_284);
x_287 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_285);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
lean_dec(x_286);
return x_287;
}
else
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_287);
if (x_289 == 0)
{
lean_object* x_290; uint8_t x_291; 
x_290 = lean_ctor_get(x_287, 0);
lean_dec(x_290);
x_291 = !lean_is_exclusive(x_288);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_288, 0);
x_293 = lean_nat_add(x_286, x_292);
lean_dec(x_292);
lean_dec(x_286);
lean_ctor_set(x_288, 0, x_293);
return x_287;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_288, 0);
lean_inc(x_294);
lean_dec(x_288);
x_295 = lean_nat_add(x_286, x_294);
lean_dec(x_294);
lean_dec(x_286);
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_287, 0, x_296);
return x_287;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_297 = lean_ctor_get(x_287, 1);
lean_inc(x_297);
lean_dec(x_287);
x_298 = lean_ctor_get(x_288, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_299 = x_288;
} else {
 lean_dec_ref(x_288);
 x_299 = lean_box(0);
}
x_300 = lean_nat_add(x_286, x_298);
lean_dec(x_298);
lean_dec(x_286);
if (lean_is_scalar(x_299)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_299;
}
lean_ctor_set(x_301, 0, x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_297);
return x_302;
}
}
}
else
{
lean_dec(x_286);
return x_287;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_283;
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
lean_dec(x_51);
lean_dec(x_40);
lean_dec(x_25);
lean_dec(x_10);
x_303 = l_Lean_Meta_isInstSubNat___redArg(x_50, x_3, x_9);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_unbox(x_304);
lean_dec(x_304);
if (x_305 == 0)
{
uint8_t x_306; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_306 = !lean_is_exclusive(x_303);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_303, 0);
lean_dec(x_307);
x_308 = lean_box(0);
lean_ctor_set(x_303, 0, x_308);
return x_303;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_303, 1);
lean_inc(x_309);
lean_dec(x_303);
x_310 = lean_box(0);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_303, 1);
lean_inc(x_312);
lean_dec(x_303);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_313 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
if (lean_obj_tag(x_314) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_313;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_ctor_get(x_314, 0);
lean_inc(x_316);
lean_dec(x_314);
x_317 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_315);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
if (lean_obj_tag(x_318) == 0)
{
lean_dec(x_316);
return x_317;
}
else
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_317);
if (x_319 == 0)
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_ctor_get(x_317, 0);
lean_dec(x_320);
x_321 = !lean_is_exclusive(x_318);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_318, 0);
x_323 = lean_nat_sub(x_316, x_322);
lean_dec(x_322);
lean_dec(x_316);
lean_ctor_set(x_318, 0, x_323);
return x_317;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_318, 0);
lean_inc(x_324);
lean_dec(x_318);
x_325 = lean_nat_sub(x_316, x_324);
lean_dec(x_324);
lean_dec(x_316);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_317, 0, x_326);
return x_317;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_327 = lean_ctor_get(x_317, 1);
lean_inc(x_327);
lean_dec(x_317);
x_328 = lean_ctor_get(x_318, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_329 = x_318;
} else {
 lean_dec_ref(x_318);
 x_329 = lean_box(0);
}
x_330 = lean_nat_sub(x_316, x_328);
lean_dec(x_328);
lean_dec(x_316);
if (lean_is_scalar(x_329)) {
 x_331 = lean_alloc_ctor(1, 1, 0);
} else {
 x_331 = x_329;
}
lean_ctor_set(x_331, 0, x_330);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_327);
return x_332;
}
}
}
else
{
lean_dec(x_316);
return x_317;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_313;
}
}
}
}
else
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; 
lean_dec(x_51);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_10);
x_333 = l_Lean_Meta_isInstMulNat(x_50, x_2, x_3, x_4, x_5, x_9);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_unbox(x_334);
lean_dec(x_334);
if (x_335 == 0)
{
uint8_t x_336; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_336 = !lean_is_exclusive(x_333);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_333, 0);
lean_dec(x_337);
x_338 = lean_box(0);
lean_ctor_set(x_333, 0, x_338);
return x_333;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_333, 1);
lean_inc(x_339);
lean_dec(x_333);
x_340 = lean_box(0);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_333, 1);
lean_inc(x_342);
lean_dec(x_333);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_343 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
if (lean_obj_tag(x_344) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_343;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
lean_dec(x_344);
x_347 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_345);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_obj_tag(x_348) == 0)
{
lean_dec(x_346);
return x_347;
}
else
{
uint8_t x_349; 
x_349 = !lean_is_exclusive(x_347);
if (x_349 == 0)
{
lean_object* x_350; uint8_t x_351; 
x_350 = lean_ctor_get(x_347, 0);
lean_dec(x_350);
x_351 = !lean_is_exclusive(x_348);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_348, 0);
x_353 = lean_nat_mul(x_346, x_352);
lean_dec(x_352);
lean_dec(x_346);
lean_ctor_set(x_348, 0, x_353);
return x_347;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_348, 0);
lean_inc(x_354);
lean_dec(x_348);
x_355 = lean_nat_mul(x_346, x_354);
lean_dec(x_354);
lean_dec(x_346);
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_347, 0, x_356);
return x_347;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_357 = lean_ctor_get(x_347, 1);
lean_inc(x_357);
lean_dec(x_347);
x_358 = lean_ctor_get(x_348, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 x_359 = x_348;
} else {
 lean_dec_ref(x_348);
 x_359 = lean_box(0);
}
x_360 = lean_nat_mul(x_346, x_358);
lean_dec(x_358);
lean_dec(x_346);
if (lean_is_scalar(x_359)) {
 x_361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_361 = x_359;
}
lean_ctor_set(x_361, 0, x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_357);
return x_362;
}
}
}
else
{
lean_dec(x_346);
return x_347;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_343;
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; 
lean_dec(x_51);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_10);
x_363 = l_Lean_Meta_isInstDivNat(x_50, x_2, x_3, x_4, x_5, x_9);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_unbox(x_364);
lean_dec(x_364);
if (x_365 == 0)
{
uint8_t x_366; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_366 = !lean_is_exclusive(x_363);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_363, 0);
lean_dec(x_367);
x_368 = lean_box(0);
lean_ctor_set(x_363, 0, x_368);
return x_363;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_363, 1);
lean_inc(x_369);
lean_dec(x_363);
x_370 = lean_box(0);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_363, 1);
lean_inc(x_372);
lean_dec(x_363);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_373 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_372);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_obj_tag(x_374) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_373;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
lean_dec(x_374);
x_377 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_375);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_dec(x_376);
return x_377;
}
else
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_377);
if (x_379 == 0)
{
lean_object* x_380; uint8_t x_381; 
x_380 = lean_ctor_get(x_377, 0);
lean_dec(x_380);
x_381 = !lean_is_exclusive(x_378);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_378, 0);
x_383 = lean_nat_div(x_376, x_382);
lean_dec(x_382);
lean_dec(x_376);
lean_ctor_set(x_378, 0, x_383);
return x_377;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_378, 0);
lean_inc(x_384);
lean_dec(x_378);
x_385 = lean_nat_div(x_376, x_384);
lean_dec(x_384);
lean_dec(x_376);
x_386 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_377, 0, x_386);
return x_377;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_387 = lean_ctor_get(x_377, 1);
lean_inc(x_387);
lean_dec(x_377);
x_388 = lean_ctor_get(x_378, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_389 = x_378;
} else {
 lean_dec_ref(x_378);
 x_389 = lean_box(0);
}
x_390 = lean_nat_div(x_376, x_388);
lean_dec(x_388);
lean_dec(x_376);
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 1, 0);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_387);
return x_392;
}
}
}
else
{
lean_dec(x_376);
return x_377;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_373;
}
}
}
}
else
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; 
lean_dec(x_51);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_10);
x_393 = l_Lean_Meta_isInstModNat___redArg(x_50, x_3, x_9);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_unbox(x_394);
lean_dec(x_394);
if (x_395 == 0)
{
uint8_t x_396; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_396 = !lean_is_exclusive(x_393);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_393, 0);
lean_dec(x_397);
x_398 = lean_box(0);
lean_ctor_set(x_393, 0, x_398);
return x_393;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_393, 1);
lean_inc(x_399);
lean_dec(x_393);
x_400 = lean_box(0);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_393, 1);
lean_inc(x_402);
lean_dec(x_393);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_403 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_402);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_403;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = lean_ctor_get(x_404, 0);
lean_inc(x_406);
lean_dec(x_404);
x_407 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_405);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
if (lean_obj_tag(x_408) == 0)
{
lean_dec(x_406);
return x_407;
}
else
{
uint8_t x_409; 
x_409 = !lean_is_exclusive(x_407);
if (x_409 == 0)
{
lean_object* x_410; uint8_t x_411; 
x_410 = lean_ctor_get(x_407, 0);
lean_dec(x_410);
x_411 = !lean_is_exclusive(x_408);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_408, 0);
x_413 = lean_nat_mod(x_406, x_412);
lean_dec(x_412);
lean_dec(x_406);
lean_ctor_set(x_408, 0, x_413);
return x_407;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_408, 0);
lean_inc(x_414);
lean_dec(x_408);
x_415 = lean_nat_mod(x_406, x_414);
lean_dec(x_414);
lean_dec(x_406);
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_407, 0, x_416);
return x_407;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_417 = lean_ctor_get(x_407, 1);
lean_inc(x_417);
lean_dec(x_407);
x_418 = lean_ctor_get(x_408, 0);
lean_inc(x_418);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_419 = x_408;
} else {
 lean_dec_ref(x_408);
 x_419 = lean_box(0);
}
x_420 = lean_nat_mod(x_406, x_418);
lean_dec(x_418);
lean_dec(x_406);
if (lean_is_scalar(x_419)) {
 x_421 = lean_alloc_ctor(1, 1, 0);
} else {
 x_421 = x_419;
}
lean_ctor_set(x_421, 0, x_420);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_417);
return x_422;
}
}
}
else
{
lean_dec(x_406);
return x_407;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_403;
}
}
}
}
else
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; 
lean_dec(x_51);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_10);
x_423 = l_Lean_Meta_isInstNatPowNat___redArg(x_50, x_3, x_9);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_unbox(x_424);
lean_dec(x_424);
if (x_425 == 0)
{
uint8_t x_426; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_426 = !lean_is_exclusive(x_423);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_423, 0);
lean_dec(x_427);
x_428 = lean_box(0);
lean_ctor_set(x_423, 0, x_428);
return x_423;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_423, 1);
lean_inc(x_429);
lean_dec(x_423);
x_430 = lean_box(0);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
return x_431;
}
}
else
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_423, 1);
lean_inc(x_432);
lean_dec(x_423);
x_433 = l_Lean_Meta_evalNat_evalPow(x_23, x_16, x_2, x_3, x_4, x_5, x_432);
return x_433;
}
}
}
}
else
{
lean_object* x_434; lean_object* x_435; uint8_t x_436; 
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_10);
x_434 = l_Lean_Meta_isInstOfNatNat(x_16, x_2, x_3, x_4, x_5, x_9);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_unbox(x_435);
lean_dec(x_435);
if (x_436 == 0)
{
uint8_t x_437; 
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_437 = !lean_is_exclusive(x_434);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_434, 0);
lean_dec(x_438);
x_439 = lean_box(0);
lean_ctor_set(x_434, 0, x_439);
return x_434;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_434, 1);
lean_inc(x_440);
lean_dec(x_434);
x_441 = lean_box(0);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
else
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_ctor_get(x_434, 1);
lean_inc(x_443);
lean_dec(x_434);
x_444 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_443);
return x_444;
}
}
}
}
else
{
lean_object* x_445; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_445 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_445;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = lean_ctor_get(x_446, 0);
lean_inc(x_448);
lean_dec(x_446);
x_449 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_447);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
if (lean_obj_tag(x_450) == 0)
{
lean_dec(x_448);
return x_449;
}
else
{
uint8_t x_451; 
x_451 = !lean_is_exclusive(x_449);
if (x_451 == 0)
{
lean_object* x_452; uint8_t x_453; 
x_452 = lean_ctor_get(x_449, 0);
lean_dec(x_452);
x_453 = !lean_is_exclusive(x_450);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; 
x_454 = lean_ctor_get(x_450, 0);
x_455 = lean_nat_add(x_448, x_454);
lean_dec(x_454);
lean_dec(x_448);
lean_ctor_set(x_450, 0, x_455);
return x_449;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_450, 0);
lean_inc(x_456);
lean_dec(x_450);
x_457 = lean_nat_add(x_448, x_456);
lean_dec(x_456);
lean_dec(x_448);
x_458 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_449, 0, x_458);
return x_449;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_459 = lean_ctor_get(x_449, 1);
lean_inc(x_459);
lean_dec(x_449);
x_460 = lean_ctor_get(x_450, 0);
lean_inc(x_460);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 x_461 = x_450;
} else {
 lean_dec_ref(x_450);
 x_461 = lean_box(0);
}
x_462 = lean_nat_add(x_448, x_460);
lean_dec(x_460);
lean_dec(x_448);
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 1, 0);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_462);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_459);
return x_464;
}
}
}
else
{
lean_dec(x_448);
return x_449;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_445;
}
}
}
else
{
lean_object* x_465; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_465 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_465;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = lean_ctor_get(x_466, 0);
lean_inc(x_468);
lean_dec(x_466);
x_469 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_467);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
if (lean_obj_tag(x_470) == 0)
{
lean_dec(x_468);
return x_469;
}
else
{
uint8_t x_471; 
x_471 = !lean_is_exclusive(x_469);
if (x_471 == 0)
{
lean_object* x_472; uint8_t x_473; 
x_472 = lean_ctor_get(x_469, 0);
lean_dec(x_472);
x_473 = !lean_is_exclusive(x_470);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; 
x_474 = lean_ctor_get(x_470, 0);
x_475 = lean_nat_sub(x_468, x_474);
lean_dec(x_474);
lean_dec(x_468);
lean_ctor_set(x_470, 0, x_475);
return x_469;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_470, 0);
lean_inc(x_476);
lean_dec(x_470);
x_477 = lean_nat_sub(x_468, x_476);
lean_dec(x_476);
lean_dec(x_468);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_469, 0, x_478);
return x_469;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_479 = lean_ctor_get(x_469, 1);
lean_inc(x_479);
lean_dec(x_469);
x_480 = lean_ctor_get(x_470, 0);
lean_inc(x_480);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_481 = x_470;
} else {
 lean_dec_ref(x_470);
 x_481 = lean_box(0);
}
x_482 = lean_nat_sub(x_468, x_480);
lean_dec(x_480);
lean_dec(x_468);
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 1, 0);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_482);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_479);
return x_484;
}
}
}
else
{
lean_dec(x_468);
return x_469;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_465;
}
}
}
else
{
lean_object* x_485; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_485 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
if (lean_obj_tag(x_486) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_485;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
x_488 = lean_ctor_get(x_486, 0);
lean_inc(x_488);
lean_dec(x_486);
x_489 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_487);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; 
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
if (lean_obj_tag(x_490) == 0)
{
lean_dec(x_488);
return x_489;
}
else
{
uint8_t x_491; 
x_491 = !lean_is_exclusive(x_489);
if (x_491 == 0)
{
lean_object* x_492; uint8_t x_493; 
x_492 = lean_ctor_get(x_489, 0);
lean_dec(x_492);
x_493 = !lean_is_exclusive(x_490);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_ctor_get(x_490, 0);
x_495 = lean_nat_mul(x_488, x_494);
lean_dec(x_494);
lean_dec(x_488);
lean_ctor_set(x_490, 0, x_495);
return x_489;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_490, 0);
lean_inc(x_496);
lean_dec(x_490);
x_497 = lean_nat_mul(x_488, x_496);
lean_dec(x_496);
lean_dec(x_488);
x_498 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_489, 0, x_498);
return x_489;
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_499 = lean_ctor_get(x_489, 1);
lean_inc(x_499);
lean_dec(x_489);
x_500 = lean_ctor_get(x_490, 0);
lean_inc(x_500);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 x_501 = x_490;
} else {
 lean_dec_ref(x_490);
 x_501 = lean_box(0);
}
x_502 = lean_nat_mul(x_488, x_500);
lean_dec(x_500);
lean_dec(x_488);
if (lean_is_scalar(x_501)) {
 x_503 = lean_alloc_ctor(1, 1, 0);
} else {
 x_503 = x_501;
}
lean_ctor_set(x_503, 0, x_502);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_499);
return x_504;
}
}
}
else
{
lean_dec(x_488);
return x_489;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_485;
}
}
}
else
{
lean_object* x_505; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_505 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
if (lean_obj_tag(x_506) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_505;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
lean_dec(x_506);
x_509 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_507);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
if (lean_obj_tag(x_510) == 0)
{
lean_dec(x_508);
return x_509;
}
else
{
uint8_t x_511; 
x_511 = !lean_is_exclusive(x_509);
if (x_511 == 0)
{
lean_object* x_512; uint8_t x_513; 
x_512 = lean_ctor_get(x_509, 0);
lean_dec(x_512);
x_513 = !lean_is_exclusive(x_510);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; 
x_514 = lean_ctor_get(x_510, 0);
x_515 = lean_nat_div(x_508, x_514);
lean_dec(x_514);
lean_dec(x_508);
lean_ctor_set(x_510, 0, x_515);
return x_509;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_510, 0);
lean_inc(x_516);
lean_dec(x_510);
x_517 = lean_nat_div(x_508, x_516);
lean_dec(x_516);
lean_dec(x_508);
x_518 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_509, 0, x_518);
return x_509;
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_519 = lean_ctor_get(x_509, 1);
lean_inc(x_519);
lean_dec(x_509);
x_520 = lean_ctor_get(x_510, 0);
lean_inc(x_520);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 x_521 = x_510;
} else {
 lean_dec_ref(x_510);
 x_521 = lean_box(0);
}
x_522 = lean_nat_div(x_508, x_520);
lean_dec(x_520);
lean_dec(x_508);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 1, 0);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_522);
x_524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_519);
return x_524;
}
}
}
else
{
lean_dec(x_508);
return x_509;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_505;
}
}
}
else
{
lean_object* x_525; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_525 = l_Lean_Meta_evalNat(x_23, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
if (lean_obj_tag(x_526) == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_525;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = lean_ctor_get(x_526, 0);
lean_inc(x_528);
lean_dec(x_526);
x_529 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_527);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
if (lean_obj_tag(x_530) == 0)
{
lean_dec(x_528);
return x_529;
}
else
{
uint8_t x_531; 
x_531 = !lean_is_exclusive(x_529);
if (x_531 == 0)
{
lean_object* x_532; uint8_t x_533; 
x_532 = lean_ctor_get(x_529, 0);
lean_dec(x_532);
x_533 = !lean_is_exclusive(x_530);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_ctor_get(x_530, 0);
x_535 = lean_nat_mod(x_528, x_534);
lean_dec(x_534);
lean_dec(x_528);
lean_ctor_set(x_530, 0, x_535);
return x_529;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_530, 0);
lean_inc(x_536);
lean_dec(x_530);
x_537 = lean_nat_mod(x_528, x_536);
lean_dec(x_536);
lean_dec(x_528);
x_538 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_529, 0, x_538);
return x_529;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_539 = lean_ctor_get(x_529, 1);
lean_inc(x_539);
lean_dec(x_529);
x_540 = lean_ctor_get(x_530, 0);
lean_inc(x_540);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 x_541 = x_530;
} else {
 lean_dec_ref(x_530);
 x_541 = lean_box(0);
}
x_542 = lean_nat_mod(x_528, x_540);
lean_dec(x_540);
lean_dec(x_528);
if (lean_is_scalar(x_541)) {
 x_543 = lean_alloc_ctor(1, 1, 0);
} else {
 x_543 = x_541;
}
lean_ctor_set(x_543, 0, x_542);
x_544 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_539);
return x_544;
}
}
}
else
{
lean_dec(x_528);
return x_529;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_525;
}
}
}
else
{
lean_object* x_545; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_10);
x_545 = l_Lean_Meta_evalNat_evalPow(x_23, x_16, x_2, x_3, x_4, x_5, x_9);
return x_545;
}
}
}
else
{
lean_object* x_546; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
x_546 = l_Lean_Meta_evalNat(x_16, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
if (lean_obj_tag(x_547) == 0)
{
return x_546;
}
else
{
uint8_t x_548; 
x_548 = !lean_is_exclusive(x_546);
if (x_548 == 0)
{
lean_object* x_549; uint8_t x_550; 
x_549 = lean_ctor_get(x_546, 0);
lean_dec(x_549);
x_550 = !lean_is_exclusive(x_547);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_547, 0);
x_552 = lean_unsigned_to_nat(1u);
x_553 = lean_nat_add(x_551, x_552);
lean_dec(x_551);
lean_ctor_set(x_547, 0, x_553);
return x_546;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_554 = lean_ctor_get(x_547, 0);
lean_inc(x_554);
lean_dec(x_547);
x_555 = lean_unsigned_to_nat(1u);
x_556 = lean_nat_add(x_554, x_555);
lean_dec(x_554);
x_557 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_546, 0, x_557);
return x_546;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_558 = lean_ctor_get(x_546, 1);
lean_inc(x_558);
lean_dec(x_546);
x_559 = lean_ctor_get(x_547, 0);
lean_inc(x_559);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 x_560 = x_547;
} else {
 lean_dec_ref(x_547);
 x_560 = lean_box(0);
}
x_561 = lean_unsigned_to_nat(1u);
x_562 = lean_nat_add(x_559, x_561);
lean_dec(x_559);
if (lean_is_scalar(x_560)) {
 x_563 = lean_alloc_ctor(1, 1, 0);
} else {
 x_563 = x_560;
}
lean_ctor_set(x_563, 0, x_562);
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_558);
return x_564;
}
}
}
else
{
return x_546;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalNat___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_evalNat___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg___lam__0), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get_uint8(x_9, 0);
x_11 = lean_ctor_get_uint8(x_9, 1);
x_12 = lean_ctor_get_uint8(x_9, 2);
x_13 = lean_ctor_get_uint8(x_9, 3);
x_14 = lean_ctor_get_uint8(x_9, 4);
x_15 = lean_ctor_get_uint8(x_9, 5);
x_16 = lean_ctor_get_uint8(x_9, 6);
x_17 = lean_ctor_get_uint8(x_9, 7);
x_18 = lean_ctor_get_uint8(x_9, 8);
x_19 = lean_ctor_get_uint8(x_9, 10);
x_20 = lean_ctor_get_uint8(x_9, 11);
x_21 = lean_ctor_get_uint8(x_9, 12);
x_22 = lean_ctor_get_uint8(x_9, 13);
x_23 = lean_ctor_get_uint8(x_9, 14);
x_24 = lean_ctor_get_uint8(x_9, 15);
x_25 = lean_ctor_get_uint8(x_9, 16);
x_26 = lean_ctor_get_uint8(x_9, 17);
x_27 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_27, 0, x_10);
lean_ctor_set_uint8(x_27, 1, x_11);
lean_ctor_set_uint8(x_27, 2, x_12);
lean_ctor_set_uint8(x_27, 3, x_13);
lean_ctor_set_uint8(x_27, 4, x_14);
lean_ctor_set_uint8(x_27, 5, x_15);
lean_ctor_set_uint8(x_27, 6, x_16);
lean_ctor_set_uint8(x_27, 7, x_17);
lean_ctor_set_uint8(x_27, 8, x_18);
lean_ctor_set_uint8(x_27, 9, x_1);
lean_ctor_set_uint8(x_27, 10, x_19);
lean_ctor_set_uint8(x_27, 11, x_20);
lean_ctor_set_uint8(x_27, 12, x_21);
lean_ctor_set_uint8(x_27, 13, x_22);
lean_ctor_set_uint8(x_27, 14, x_23);
lean_ctor_set_uint8(x_27, 15, x_24);
lean_ctor_set_uint8(x_27, 16, x_25);
lean_ctor_set_uint8(x_27, 17, x_26);
x_28 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_shift_left(x_31, x_30);
x_33 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_34 = lean_uint64_lor(x_32, x_33);
x_35 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_36 = lean_ctor_get(x_4, 1);
x_37 = lean_ctor_get(x_4, 2);
x_38 = lean_ctor_get(x_4, 3);
x_39 = lean_ctor_get(x_4, 4);
x_40 = lean_ctor_get(x_4, 5);
x_41 = lean_ctor_get(x_4, 6);
x_42 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
x_44 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
lean_ctor_set_uint64(x_44, sizeof(void*)*7, x_34);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 8, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 9, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 10, x_43);
x_45 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_44, x_5, x_6, x_7, x_8);
lean_dec(x_44);
return x_45;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_matchesInstance___lam__0___boxed), 8, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_9, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchesInstance___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_matchesInstance___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
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
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isOffset_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_8);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = lean_mk_string_unchecked("Nat", 3, 3);
x_19 = lean_mk_string_unchecked("succ", 4, 4);
lean_inc(x_18);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isApp(x_17);
if (x_22 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
x_84 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_85 = lean_mk_string_unchecked("add", 3, 3);
lean_inc(x_85);
x_86 = l_Lean_Name_mkStr2(x_18, x_85);
x_87 = l_Lean_Expr_isConstOf(x_84, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Expr_isApp(x_84);
if (x_88 == 0)
{
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_inc(x_84);
x_89 = l_Lean_Expr_appFnCleanup___redArg(x_84);
x_90 = l_Lean_Expr_isApp(x_89);
if (x_90 == 0)
{
lean_dec(x_89);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_Expr_appFnCleanup___redArg(x_89);
x_93 = lean_mk_string_unchecked("Add", 3, 3);
x_94 = l_Lean_Name_mkStr2(x_93, x_85);
x_95 = l_Lean_Expr_isConstOf(x_92, x_94);
lean_dec(x_94);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = l_Lean_Expr_isApp(x_92);
if (x_96 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = l_Lean_Expr_appFnCleanup___redArg(x_92);
x_98 = l_Lean_Expr_isApp(x_97);
if (x_98 == 0)
{
lean_dec(x_97);
lean_dec(x_91);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = l_Lean_Expr_appFnCleanup___redArg(x_97);
x_100 = lean_mk_string_unchecked("HAdd", 4, 4);
x_101 = lean_mk_string_unchecked("hAdd", 4, 4);
x_102 = l_Lean_Name_mkStr2(x_100, x_101);
x_103 = l_Lean_Expr_isConstOf(x_99, x_102);
lean_dec(x_102);
lean_dec(x_99);
if (x_103 == 0)
{
lean_dec(x_91);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_13;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_10);
x_104 = l_Lean_Nat_mkInstHAdd;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_105 = l_Lean_Meta_matchesInstance(x_91, x_104, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = lean_box(0);
lean_ctor_set(x_105, 0, x_110);
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
lean_dec(x_105);
x_24 = x_16;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_114;
goto block_83;
}
}
else
{
uint8_t x_115; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_92);
lean_dec(x_10);
x_119 = l_Lean_Nat_mkInstAdd;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_120 = l_Lean_Meta_matchesInstance(x_91, x_119, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
uint8_t x_123; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_120);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_120, 0);
lean_dec(x_124);
x_125 = lean_box(0);
lean_ctor_set(x_120, 0, x_125);
return x_120;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_dec(x_120);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_120, 1);
lean_inc(x_129);
lean_dec(x_120);
x_24 = x_16;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_129;
goto block_83;
}
}
else
{
uint8_t x_130; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_120);
if (x_130 == 0)
{
return x_120;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_120, 0);
x_132 = lean_ctor_get(x_120, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_120);
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
else
{
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_10);
x_24 = x_16;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_9;
goto block_83;
}
block_83:
{
lean_object* x_30; 
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_30 = l_Lean_Meta_evalNat(x_24, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_23, x_25, x_26, x_27, x_28, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_nat_add(x_45, x_40);
lean_dec(x_40);
lean_dec(x_45);
lean_ctor_set(x_43, 1, x_46);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_41, 0, x_31);
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_nat_add(x_48, x_40);
lean_dec(x_40);
lean_dec(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_31, 0, x_50);
lean_ctor_set(x_41, 0, x_31);
return x_41;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_55 = x_51;
} else {
 lean_dec_ref(x_51);
 x_55 = lean_box(0);
}
x_56 = lean_nat_add(x_54, x_40);
lean_dec(x_40);
lean_dec(x_54);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_31, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_31);
lean_ctor_set(x_58, 1, x_52);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_31);
lean_dec(x_40);
x_59 = !lean_is_exclusive(x_41);
if (x_59 == 0)
{
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_41, 0);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_41);
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
x_63 = lean_ctor_get(x_31, 0);
lean_inc(x_63);
lean_dec(x_31);
x_64 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_23, x_25, x_26, x_27, x_28, x_38);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
x_71 = lean_nat_add(x_69, x_63);
lean_dec(x_63);
lean_dec(x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (lean_is_scalar(x_67)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_67;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_63);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_77 = x_64;
} else {
 lean_dec_ref(x_64);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
x_79 = !lean_is_exclusive(x_30);
if (x_79 == 0)
{
return x_30;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_30, 0);
x_81 = lean_ctor_get(x_30, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_30);
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
lean_object* x_134; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
x_134 = l___private_Lean_Meta_Offset_0__Lean_Meta_getOffset(x_16, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_136, 1);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_add(x_138, x_139);
lean_dec(x_138);
lean_ctor_set(x_136, 1, x_140);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_136);
lean_ctor_set(x_134, 0, x_141);
return x_134;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_136, 0);
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_136);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_add(x_143, x_144);
lean_dec(x_143);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_134, 0, x_147);
return x_134;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_134, 0);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_134);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_152 = x_148;
} else {
 lean_dec_ref(x_148);
 x_152 = lean_box(0);
}
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_add(x_151, x_153);
lean_dec(x_151);
if (lean_is_scalar(x_152)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_152;
}
lean_ctor_set(x_155, 0, x_150);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_149);
return x_157;
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_134);
if (x_158 == 0)
{
return x_134;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_134, 0);
x_160 = lean_ctor_get(x_134, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_134);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_evalNat(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
x_20 = lean_box(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l___private_Lean_Meta_Offset_0__Lean_Meta_isNatZero(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_mkNatLit(x_2);
x_16 = l_Lean_mkNatAdd(x_1, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_mkNatLit(x_2);
x_19 = l_Lean_mkNatAdd(x_1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = l_Lean_mkNatLit(x_2);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_mkNatLit(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_mk_string_unchecked("Nat", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_12, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux___boxed), 7, 2);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_15, x_17, x_3, x_4, x_5, x_6, x_10);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_box(2);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_box(2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_is_expr_def_eq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Bool_toLBool(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
x_17 = l_Bool_toLBool(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_getConfig(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, 8);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(2);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Meta_isOffset_x3f(x_1, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_31; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_31 = l_Lean_Meta_evalNat(x_1, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(2);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_41 = l_Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_44 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = lean_box(2);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_box(2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_nat_dec_eq(x_40, x_53);
lean_dec(x_53);
lean_dec(x_40);
x_55 = l_Bool_toLBool(x_54);
x_56 = lean_box(x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__2___boxed), 6, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_57, x_3, x_4, x_5, x_6, x_52);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
return x_44;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_44);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_2);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
lean_dec(x_42);
x_64 = lean_ctor_get(x_41, 1);
lean_inc(x_64);
lean_dec(x_41);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_nat_dec_le(x_66, x_40);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_40);
x_68 = lean_box(0);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__2___boxed), 6, 1);
lean_closure_set(x_69, 0, x_68);
x_70 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_69, x_3, x_4, x_5, x_6, x_64);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_nat_sub(x_40, x_66);
lean_dec(x_66);
lean_dec(x_40);
x_72 = l_Lean_mkNatLit(x_71);
x_21 = x_72;
x_22 = x_65;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_64;
goto block_30;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_41);
if (x_73 == 0)
{
return x_41;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_41, 0);
x_75 = lean_ctor_get(x_41, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
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
uint8_t x_77; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_31);
if (x_77 == 0)
{
return x_31;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_31, 0);
x_79 = lean_ctor_get(x_31, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_31);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_19, 0);
lean_inc(x_81);
lean_dec(x_19);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_84 = l_Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_87 = l_Lean_Meta_evalNat(x_2, x_3, x_4, x_5, x_6, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
lean_dec(x_90);
x_91 = lean_box(2);
lean_ctor_set(x_87, 0, x_91);
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_box(2);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
lean_dec(x_87);
x_96 = lean_ctor_get(x_88, 0);
lean_inc(x_96);
lean_dec(x_88);
x_97 = lean_nat_dec_le(x_83, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_96);
lean_dec(x_83);
lean_dec(x_82);
x_98 = lean_box(0);
x_99 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__2___boxed), 6, 1);
lean_closure_set(x_99, 0, x_98);
x_100 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_99, x_3, x_4, x_5, x_6, x_95);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_nat_sub(x_96, x_83);
lean_dec(x_83);
lean_dec(x_96);
x_102 = l_Lean_mkNatLit(x_101);
x_21 = x_82;
x_22 = x_102;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_95;
goto block_30;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_87);
if (x_103 == 0)
{
return x_87;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_87, 0);
x_105 = lean_ctor_get(x_87, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_87);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_2);
x_107 = lean_ctor_get(x_85, 0);
lean_inc(x_107);
lean_dec(x_85);
x_108 = lean_ctor_get(x_84, 1);
lean_inc(x_108);
lean_dec(x_84);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_nat_dec_eq(x_83, x_110);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = lean_nat_dec_lt(x_83, x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_nat_sub(x_83, x_110);
lean_dec(x_110);
lean_dec(x_83);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_114 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_82, x_113, x_3, x_4, x_5, x_6, x_108);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_21 = x_115;
x_22 = x_109;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_116;
goto block_30;
}
else
{
uint8_t x_117; 
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_114);
if (x_117 == 0)
{
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_114);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_nat_sub(x_110, x_83);
lean_dec(x_83);
lean_dec(x_110);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_122 = l___private_Lean_Meta_Offset_0__Lean_Meta_mkOffset(x_109, x_121, x_3, x_4, x_5, x_6, x_108);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_21 = x_82;
x_22 = x_123;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_124;
goto block_30;
}
else
{
uint8_t x_125; 
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_122);
if (x_125 == 0)
{
return x_122;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_122, 0);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_122);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
else
{
lean_dec(x_110);
lean_dec(x_83);
x_21 = x_82;
x_22 = x_109;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_108;
goto block_30;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_84);
if (x_129 == 0)
{
return x_84;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_84, 0);
x_131 = lean_ctor_get(x_84, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_84);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_isDefEqOffset___lam__1), 7, 2);
lean_closure_set(x_28, 0, x_21);
lean_closure_set(x_28, 1, x_22);
x_29 = l_Lean_Meta_isDefEqOffset___lam__0(x_1, x_28, x_23, x_24, x_25, x_26, x_27);
return x_29;
}
}
else
{
uint8_t x_133; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_18);
if (x_133 == 0)
{
return x_18;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_18, 0);
x_135 = lean_ctor_get(x_18, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_18);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isDefEqOffset___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_Meta_isDefEqOffset___lam__2(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init_Control_Option(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
